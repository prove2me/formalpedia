-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_product_grid_pathwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:47:28.782636+00:00
-- url     : https://prove2.me/submissions/89f025f0-c88a-4957-9e1e-81495b94447a

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_product
import Theorems.Thm_Kyprianou_Ch04_kw48_discrete_product_summation
import Theorems.Thm_Kyprianou_Ch04_kw48_product_grid_transfer
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The correction limit implies the signed actual process increment limit. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b : NNReal) (w : Ω)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (hCorr : Tendsto (fun n => C L Psi alpha beta (u n) (N n) w)
      atTop (nhds (Complex.I*((beta-alpha:Real):Complex)*
        (S L beta b w-S L beta a w) -
        Psi alpha*(J L alpha beta b w-J L alpha beta a w)))) :
    Tendsto (fun n => Q L Psi alpha beta (u n) (N n) w)
      atTop (nhds (M L Psi alpha beta a w-M L Psi alpha beta b w)) := by
  have hGrid (n : Nat) :
      Q L Psi alpha beta (u n) (N n) w+C L Psi alpha beta (u n) (N n) w =
        Z L alpha beta b w-Z L alpha beta a w := by
    have h := Kyprianou.Ch04.kw48_discrete_product_summation
      (fun i => E L Psi alpha (u n i) w)
      (fun i => H L Psi alpha beta (u n i) w) (N n)
    rw [h0 n,hN n,Kyprianou.Ch04.kw48_exp_product,
      Kyprianou.Ch04.kw48_exp_product] at h
    exact h
  have h := Kyprianou.Ch04.kw48_product_grid_transfer _ _ _ _ _ hGrid hCorr
  convert h using 1
  congr 1
  unfold M
  push_cast
  ring
