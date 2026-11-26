-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_stieltjes_left_uniform_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:38:03.558486+00:00
-- url     : https://prove2.me/submissions/26d8ed78-68d4-4024-9900-3a0a2507cd09

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_record_grid_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_S_zero
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The exact left-endpoint Stieltjes sums in the exercise
converge pathwise at every time to the record-level primitive. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
    (t : NNReal) :
    Tendsto (fun n : Nat => ∑ k ∈ Finset.range n,
      let u : NNReal := t*(k:NNReal)/(n:NNReal)
      let v : NNReal := t*((k+1:Nat):NNReal)/(n:NNReal)
      Z L alpha beta u w *
        ((runningSup L v w-runningSup L u w : Real):Complex))
      atTop (nhds (S L beta t w)) := by
  let Q : Nat → Complex := fun n => ∑ i ∈ Finset.range n,
    Z L alpha beta (t*(i:NNReal)/(n:NNReal)) w *
      ((runningSup L (t*((i+1:Nat):NNReal)/(n:NNReal)) w -
        runningSup L (t*(i:NNReal)/(n:NNReal)) w:Real):Complex)
  let u : Nat → Nat → NNReal := fun n i =>
    0+(t-0)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
  obtain ⟨hu,h0,hN,hT,hMesh,hDelta⟩ :=
    Kyprianou.Ch04.kw47_capped_uniform_grid 0 t (show 0 ≤ t from zero_le)
  have h := Kyprianou.Ch04.kw48_record_grid_limit L alpha beta w 0 t
    (show 0 ≤ t from zero_le) u (fun n => n+1) hu h0 hN
    (fun n => ((t:Real)-(0:NNReal):Real)/((n+1:Nat):Real)) hDelta
    (fun n i hi => le_of_eq (hMesh n i hi)) false
  simp only [Bool.false_eq_true,if_false,Kyprianou.Ch04.kw48_S_zero,sub_zero] at h
  have heq (n : Nat) : (∑ i ∈ Finset.range (n+1),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
        Z L alpha beta (u n i) w) = Q (n+1) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [u,zero_add,tsub_zero,min_eq_left (le_of_lt hi'),
      min_eq_left (Nat.succ_le_of_lt hi'),Complex.real_smul]
    ring
  simp only [heq] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h
