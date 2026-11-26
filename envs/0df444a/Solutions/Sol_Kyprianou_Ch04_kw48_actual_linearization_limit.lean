-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_actual_linearization_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:55:05.846038+00:00
-- url     : https://prove2.me/submissions/4b2fa9e1-a535-498c-b26e-d3826d9003b9

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_grid_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_log_weight_grid_variation
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual continuous complex log-weight admits a vanishing
first-order approximation error on every vanishing-mesh grid. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (N n), Z L alpha beta (u n (i+1)) w *
        (1-Complex.exp (-(G L Psi alpha beta (u n (i+1)) w-
          G L Psi alpha beta (u n i) w)))) -
      (∑ i ∈ Finset.range (N n), Z L alpha beta (u n (i+1)) w *
        (G L Psi alpha beta (u n (i+1)) w-G L Psi alpha beta (u n i) w)))
      atTop (nhds 0) := by
  let U : NNReal → Real := fun t => runningSup L t w
  let g : Real → Complex := fun r =>
    Complex.I*((beta-alpha:Real):Complex)*(U r.toNNReal:Complex)-
      (r:Complex)*Psi alpha
  let z : Nat → Nat → Complex := fun n i => Z L alpha beta (u n (i+1)) w
  let V : Real := |beta-alpha| * (U b-U a)+‖Psi alpha‖*((b:Real)-(a:Real))
  have hUc : Continuous (fun r : Real => U r.toNNReal) :=
    (runningSup_continuous_actual L w).comp continuous_real_toNNReal
  have hg : Continuous g := by
    exact (continuous_const.mul (Complex.continuous_ofReal.comp hUc)).sub
      (Complex.continuous_ofReal.mul continuous_const)
  have hmono (n : Nat) : Monotone (fun i => (u n i:Real)) :=
    fun i j hij => by exact_mod_cast hu n hij
  have hV : 0 ≤ V := add_nonneg
    (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr
      ((runningSup_monotone_and_path_le L w).1 hab)))
    (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hab)))
  have hZ (n i : Nat) : ‖z n i‖ ≤ 1 :=
    le_of_eq (Kyprianou.Ch04.kw48_norm_Z L alpha beta (u n (i+1)) w)
  have hVar (n : Nat) : (∑ i ∈ Finset.range (N n),
      ‖g (u n (i+1):Real)-g (u n i:Real)‖) ≤ V := by
    simpa only [g,U,V,G,Real.toNNReal_coe,h0 n,hN n] using
      Kyprianou.Ch04.kw48_log_weight_grid_variation L Psi alpha beta w
        (u n) (N n) (hu n)
  have h := Kyprianou.Ch04.kw48_exp_grid_linearization_limit
    (a:Real) (b:Real) g hg.continuousOn
    (fun n i => (u n i:Real)) N hmono (fun n => by rw [h0 n])
    (fun n => by rw [hN n]) delta hDelta hMesh z hZ V hV hVar
  simpa only [g,z,U,G,Real.toNNReal_coe] using h
