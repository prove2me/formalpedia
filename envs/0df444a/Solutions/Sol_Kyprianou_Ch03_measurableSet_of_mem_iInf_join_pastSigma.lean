-- Prove2me | solution 1 for Kyprianou.Ch03.measurableSet_of_mem_iInf_join_pastSigma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:17:23.338519+00:00
-- url     : https://prove2.me/submissions/1d0ae003-0fa6-4cb3-ac92-a4330bbffdab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_le_join_germSigma_space

open MeasureTheory ProbabilityTheory DurrettProbability Set MeasurableSpace
open scoped NNReal

set_option autoImplicit false
set_option warn.classDefReducibility false

/-!
Sketch: setwise Inf-join → join-germ from the space-level lattice inequality.

`measurableSet_iInf` turns the pointwise hypothesis into Inf-join measurability;
`le_def` + Open child `iInf_join_pastSigma_le_join_germSigma_space` transfers to join-germ.
-/

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real)
    {s : Set Omega}
    (h : ∀ ε : NNReal, 0 < ε → @MeasurableSet Omega (G ⊔ pastSigma Y ε) s) :
    @MeasurableSet Omega (G ⊔ germSigma Y) s := by
  have hsInf :
      @MeasurableSet Omega (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) s := by
    rw [measurableSet_iInf]
    intro ε
    rw [measurableSet_iInf]
    intro hε
    exact h ε hε
  have hle := iInf_join_pastSigma_le_join_germSigma_space G Y
  exact MeasurableSpace.le_def.mp hle s hsInf
