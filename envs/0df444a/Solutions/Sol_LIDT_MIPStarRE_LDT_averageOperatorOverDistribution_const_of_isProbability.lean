-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_const_of_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:43:40.382737+00:00
-- url     : https://prove2.me/submissions/0fb4407b-fde4-4ea7-bc6c-56f074e506da

-- Generated proof for MIPStarRE.LDT.averageOperatorOverDistribution_const_of_isProbability.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

end LIDT

open LIDT
/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support weighted distributions,
a probability predicate, push-forward distributions, weighted-sum linear maps,
averaging, uniform distribution, and outcome summation.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

theorem solution {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (h𝒟 : 𝒟.IsProbability) (A : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution 𝒟 (fun _ : α => A) = A := by
  rw [_root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution_const, h𝒟.weight_sum_eq_one]
  simp
