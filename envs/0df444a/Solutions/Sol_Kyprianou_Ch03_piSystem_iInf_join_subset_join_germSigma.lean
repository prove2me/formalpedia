-- Prove2me | solution 1 for Kyprianou.Ch03.piSystem_iInf_join_subset_join_germSigma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:06:34.203209+00:00
-- url     : https://prove2.me/submissions/29729080-2a06-4e89-b081-09e9a6e17fc3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_measurableSet_of_mem_iInf_join_pastSigma

open MeasureTheory ProbabilityTheory DurrettProbability Set MeasurableSpace
open scoped NNReal

set_option autoImplicit false
set_option warn.classDefReducibility false
set_option linter.unusedVariables false

/-!
Sketch: π-system membership in join-germ.

Any `s ∈ C` is `generateFrom C`-measurable; rewrite via `hgen` to the Inf-join;
transfer along `iInf₂_le` to each `G ⊔ pastSigma Y ε`; apply the setwise Open child
`measurableSet_of_mem_iInf_join_pastSigma`.
-/

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real)
    (C : Set (Set Omega))
    (_hC : IsPiSystem C)
    (hgen : MeasurableSpace.generateFrom C =
      (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε)) :
    ∀ s ∈ C, @MeasurableSet Omega (G ⊔ germSigma Y) s := by
  intro s hs
  have hsInf :
      @MeasurableSet Omega (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) s := by
    rw [← hgen]
    exact measurableSet_generateFrom hs
  refine measurableSet_of_mem_iInf_join_pastSigma G Y ?_
  intro ε hε
  have hle :
      (⨅ ε' : NNReal, ⨅ (_ : 0 < ε'), G ⊔ pastSigma Y ε') ≤ G ⊔ pastSigma Y ε :=
    iInf₂_le ε hε
  exact MeasurableSpace.le_def.mp hle s hsInf
