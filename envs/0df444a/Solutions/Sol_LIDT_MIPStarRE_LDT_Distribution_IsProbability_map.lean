-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Distribution.IsProbability.map
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:45:04.716062+00:00
-- url     : https://prove2.me/submissions/63fba58a-f3b3-4961-949f-b37c882239ee

-- Generated proof for MIPStarRE.LDT.Distribution.IsProbability.map.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_map_totalWeight

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

theorem solution {α β : Type*} [DecidableEq β]
    {𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α} (h𝒟 : 𝒟.IsProbability) (e : α → β) :
    (𝒟.map e).IsProbability := by
  simpa [_root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability, _root_.LIDT.MIPStarRE.LDT.Distribution.map_totalWeight] using h𝒟
