-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_actual_grid_correction_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:37:36.870569+00:00
-- url     : https://prove2.me/submissions/ab12f505-3729-441d-b6f0-d935a48a33a1

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_actual_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_linear_sum_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_correction_cell
import Theorems.Thm_Kyprianou_Ch04_kw48_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw48_record_grid_limit
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual right-point product correction converges to the two
Stieltjes and time primitives on every vanishing-mesh grid. -/
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
    Tendsto (fun n => C L Psi alpha beta (u n) (N n) w)
      atTop (nhds (Complex.I*((beta-alpha:Real):Complex)*
        (S L beta b w-S L beta a w)-
        Psi alpha*(J L alpha beta b w-J L alpha beta a w))) := by
  have hTime := Kyprianou.Ch04.kw48_time_quadrature L alpha beta w a b hab
    u N hu h0 hN delta hDelta hMesh
  have hRecord := Kyprianou.Ch04.kw48_record_grid_limit L alpha beta w a b hab
    u N hu h0 hN delta hDelta hMesh true
  simp only [if_true] at hRecord
  have hLin := Kyprianou.Ch04.kw48_linear_sum_limit L Psi alpha beta w a b
    u N hTime hRecord
  have hErr := Kyprianou.Ch04.kw48_actual_linearization_limit L Psi alpha beta
    w a b hab u N hu h0 hN delta hDelta hMesh
  have hEq (n : Nat) : C L Psi alpha beta (u n) (N n) w =
      ∑ i ∈ Finset.range (N n), Z L alpha beta (u n (i+1)) w*
        (1-Complex.exp (-(G L Psi alpha beta (u n (i+1)) w-
          G L Psi alpha beta (u n i) w))) := by
    unfold C
    apply Finset.sum_congr rfl
    intro i hi
    exact Kyprianou.Ch04.kw48_grid_correction_cell L Psi alpha beta
      (u n i) (u n (i+1)) w
  simp_rw [← hEq] at hErr
  have h := hErr.add hLin
  simpa only [sub_add_cancel,zero_add] using h
