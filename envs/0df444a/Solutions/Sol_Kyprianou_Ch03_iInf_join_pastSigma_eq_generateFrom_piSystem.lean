-- Prove2me | solution 1 for Kyprianou.Ch03.iInf_join_pastSigma_eq_generateFrom_piSystem
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:54:09.851644+00:00
-- url     : https://prove2.me/submissions/64451816-333c-4704-b8a5-8a41eba82a7c

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open MeasureTheory ProbabilityTheory DurrettProbability Set MeasurableSpace
open scoped NNReal

set_option autoImplicit false
set_option warn.classDefReducibility false

/-!
Leaf: every measurable space `m` equals `generateFrom` of its measurable sets,
and that collection is a π-system. Instantiate at
`m = ⨅_{ε>0}(G ⊔ pastSigma Y ε)`.
-/

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    ∃ C : Set (Set Omega),
      IsPiSystem C ∧
        MeasurableSpace.generateFrom C =
          (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) := by
  let m : MeasurableSpace Omega :=
    ⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε
  refine ⟨{s | @MeasurableSet Omega m s}, ?_, ?_⟩
  · intro s hs t ht _hne
    have hs' : @MeasurableSet Omega m s := hs
    have ht' : @MeasurableSet Omega m t := ht
    exact hs'.inter ht'
  · exact (@generateFrom_measurableSet Omega m).symm ▸ rfl
