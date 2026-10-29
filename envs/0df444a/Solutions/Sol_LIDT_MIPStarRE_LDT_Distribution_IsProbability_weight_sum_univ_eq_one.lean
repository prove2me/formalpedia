-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Distribution.IsProbability.weight_sum_univ_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:43:40.268611+00:00
-- url     : https://prove2.me/submissions/a97a180d-5905-4951-8ade-d22f5c304aa1

-- Generated proof for MIPStarRE.LDT.Distribution.IsProbability.weight_sum_univ_eq_one.
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






open LIDT.MIPStarRE.LDT.Distribution.IsProbability

theorem solution {α : Type*} [Fintype α]
    {𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α} (h𝒟 : 𝒟.IsProbability) :
    (∑ a : α, 𝒟.weight a) = 1 := by
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.sum_univ_eq_sum_support 𝒟 𝒟.weight 𝒟.outsideSupport]
  exact h𝒟.weight_sum_eq_one
