-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_uniform_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:43:40.532744+00:00
-- url     : https://prove2.me/submissions/1b18fa5a-cac9-4fc2-abcc-a6bf35dbd5b4

-- Generated proof for MIPStarRE.LDT.averageOperatorOverDistribution_uniform_equiv.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

end LIDT

open LIDT
/-!
# Average lemmas for finite-support distributions

This module contains the finite-sum and uniform-average lemmas for the project
`Distribution` type.  The primitive distribution definitions, uniform
distributions, and total variation distance live in
`MIPStarRE.LDT.Basic.Distribution`.

## Main declarations

The main results are the algebraic rules for `avgOver`, scalar and
operator-valued forms of the module-valued finite-sum rules for uniform
distributions, and the comparison between finite uniform averages and Mathlib
uniform probability mass functions.

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

/-! ### Averaging infrastructure

Linearity proofs use `Distribution.weightedSumLinearMap`; order and support
estimates use Mathlib's `Finset.sum` API. -/

theorem solution
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (f : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f =
      _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
        (fun b => f (e.symm b)) := by
  simpa [_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution] using
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution_sum_smul_equiv (e := e) (f := f)
