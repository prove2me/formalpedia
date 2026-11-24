-- Prove2me | solution 1 for Kyprianou.Ch03.iInf_join_pastSigma_le_join_germSigma_space
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:31:20.67635+00:00
-- url     : https://prove2.me/submissions/3694b329-959d-474d-8cd6-bd11a496f5d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_exists_piSystem_iInf_join_pastSigma_in_join_germ

open MeasureTheory ProbabilityTheory DurrettProbability Set MeasurableSpace
open scoped NNReal

set_option autoImplicit false
set_option warn.classDefReducibility false

/-!
Sketch: space-level Inf-join ≤ join-germ.

Open child: `exists_piSystem_iInf_join_pastSigma_in_join_germ` — ∃ π-system generating
the Inf-join with every member in `G ⊔ germ` (Dynkin/Williams-sensitive core).

Glue: `MeasurableSpace.generateFrom_le`.
-/

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ≤ G ⊔ germSigma Y := by
  obtain ⟨C, _, hgen, hsub⟩ := exists_piSystem_iInf_join_pastSigma_in_join_germ G Y
  have hle : MeasurableSpace.generateFrom C ≤ G ⊔ germSigma Y :=
    MeasurableSpace.generateFrom_le hsub
  rwa [hgen] at hle
