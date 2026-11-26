-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_linear_sum_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:55:05.388894+00:00
-- url     : https://prove2.me/submissions/137a7f41-bcd8-4a99-ba5b-8ac9b71b06f4

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The linearised complex correction is the prescribed linear
combination of the convergent record and time quadratures. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (w : Ω) (a b : NNReal)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hTime : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((u n (i+1):Real)-(u n i:Real)) • Z L alpha beta (u n (i+1)) w)
      atTop (nhds (J L alpha beta b w-J L alpha beta a w)))
    (hRecord : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
        Z L alpha beta (u n (i+1)) w)
      atTop (nhds (S L beta b w-S L beta a w))) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      Z L alpha beta (u n (i+1)) w *
        (G L Psi alpha beta (u n (i+1)) w-G L Psi alpha beta (u n i) w))
      atTop (nhds (Complex.I*((beta-alpha:Real):Complex)*
        (S L beta b w-S L beta a w)-
        Psi alpha*(J L alpha beta b w-J L alpha beta a w))) := by
  have hEq (n : Nat) : (∑ i ∈ Finset.range (N n),
      Z L alpha beta (u n (i+1)) w *
        (G L Psi alpha beta (u n (i+1)) w-G L Psi alpha beta (u n i) w)) =
      Complex.I*((beta-alpha:Real):Complex)*
        (∑ i ∈ Finset.range (N n),
          (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
            Z L alpha beta (u n (i+1)) w) -
      Psi alpha*(∑ i ∈ Finset.range (N n),
        ((u n (i+1):Real)-(u n i:Real)) • Z L alpha beta (u n (i+1)) w) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold G
    simp only [Complex.real_smul,Complex.ofReal_sub]
    ring
  simp_rw [hEq]
  exact (tendsto_const_nhds.mul hRecord).sub (tendsto_const_nhds.mul hTime)
