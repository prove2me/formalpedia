-- Prove2me | solution 1 for MonotoneCompStatics.LinearPerturb.increasingDifferences_singleCrossing
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:48:05.52444+00:00
-- url     : https://prove2.me/submissions/3edd8396-b501-43b9-a1ef-0d6620892af2

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

theorem solution {X T : Type*} [Lattice X] [PartialOrder T]
    (f : X → T → ℝ)
    (hf : Supermodularity.Monotonicity.IncreasingDifferencesOn f Set.univ) :
    MonotoneCompStatics.Monotonicity.SingleCrossing f := by
  intro x' x'' hx t' t'' ht
  have hd := hf ht (a := x'') (b := x') (by simp) (by simp) hx.le
  constructor <;> intro hi <;> linarith

#print axioms solution
