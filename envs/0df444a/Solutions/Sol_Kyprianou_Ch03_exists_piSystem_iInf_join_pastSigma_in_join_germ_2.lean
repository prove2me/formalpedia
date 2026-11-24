-- Prove2me | solution 2 for Kyprianou.Ch03.exists_piSystem_iInf_join_pastSigma_in_join_germ
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T10:02:58.057709+00:00
-- url     : https://prove2.me/submissions/c1c2a8b3-a119-428e-9cc1-34307c7cc0cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_le_join_germSigma_lattice

open MeasureTheory ProbabilityTheory DurrettProbability Set MeasurableSpace
open scoped NNReal

set_option autoImplicit false
set_option warn.classDefReducibility false

/-!
Sketch: `exists_piSystem_iInf_join_pastSigma_in_join_germ`.

Take `C = {s | MeasurableSet[Inf-join] s}` (π-system; `generateFrom_measurableSet`).
Open child `iInf_join_pastSigma_le_join_germSigma_lattice` transfers membership into
`G ⊔ germ`. Equivalence: such a `C` exists iff the lattice inequality holds.
-/

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    ∃ C : Set (Set Omega),
      IsPiSystem C ∧
        MeasurableSpace.generateFrom C =
          (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ∧
          (∀ s ∈ C, @MeasurableSet Omega (G ⊔ germSigma Y) s) := by
  let m : MeasurableSpace Omega :=
    ⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε
  refine ⟨{s | @MeasurableSet Omega m s}, ?_, ?_, ?_⟩
  · intro s hs t ht _hne
    have hs' : @MeasurableSet Omega m s := hs
    have ht' : @MeasurableSet Omega m t := ht
    exact hs'.inter ht'
  · exact (@generateFrom_measurableSet Omega m).symm ▸ rfl
  · intro s hs
    exact MeasurableSpace.le_def.mp (iInf_join_pastSigma_le_join_germSigma_lattice G Y) s hs
