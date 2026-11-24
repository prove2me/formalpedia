-- Prove2me | solution 1 for Kyprianou.Ch03.iInf_join_pastSigma_le_join_germSigma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:46:29.807972+00:00
-- url     : https://prove2.me/submissions/14a59bfd-d78b-4d06-af1d-2a65048be064
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_eq_generateFrom_piSystem
import Theorems.Thm_Kyprianou_Ch03_piSystem_iInf_join_subset_join_germSigma

open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal

set_option autoImplicit false
set_option warn.classDefReducibility false

/-!
Sketch: `iInf_join_pastSigma_le_join_germSigma` via π-system + `generateFrom_le`.

Open children:
1. `iInf_join_pastSigma_eq_generateFrom_piSystem` — Inf-join = `generateFrom C` for a π-system `C`
2. `piSystem_iInf_join_subset_join_germSigma` — every set of `C` lies in `G ⊔ germSigma Y`

Glue: `MeasurableSpace.generateFrom_le` yields the Inf-join ≤ join-germ.
-/

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ≤ G ⊔ germSigma Y := by
  obtain ⟨C, hpi, hgen⟩ := iInf_join_pastSigma_eq_generateFrom_piSystem G Y
  have hsub := piSystem_iInf_join_subset_join_germSigma G Y C hpi hgen
  have hle : MeasurableSpace.generateFrom C ≤ G ⊔ germSigma Y :=
    MeasurableSpace.generateFrom_le hsub
  rwa [hgen] at hle
