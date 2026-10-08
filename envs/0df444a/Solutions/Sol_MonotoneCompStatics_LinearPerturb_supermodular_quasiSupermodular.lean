-- Prove2me | solution 1 for MonotoneCompStatics.LinearPerturb.supermodular_quasiSupermodular
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:01.841564+00:00
-- url     : https://prove2.me/submissions/9a8c63e5-c5f1-43e7-b6c8-f7999b30a99b

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

theorem solution {X : Type*} [Lattice X] (g : X → ℝ)
    (hg : Supermodularity.Monotonicity.SupermodularOn g Set.univ) :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn g Set.univ  := by
  intro x hx y hy
  have h := hg hx hy
  constructor <;> intro hxy <;> linarith

#print axioms solution
