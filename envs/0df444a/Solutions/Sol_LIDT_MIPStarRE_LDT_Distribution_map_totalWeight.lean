-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Distribution.map_totalWeight
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:43:40.176705+00:00
-- url     : https://prove2.me/submissions/c5dd8943-9a5f-43fc-8c3c-a47bcb646c74

-- Generated proof for MIPStarRE.LDT.Distribution.map_totalWeight.
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



open LIDT.MIPStarRE.LDT.Distribution

theorem solution {α β : Type*} [DecidableEq β]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (e : α → β) :
    (𝒟.map e).totalWeight = 𝒟.totalWeight := by
  simpa [_root_.LIDT.MIPStarRE.LDT.Distribution.totalWeight, _root_.LIDT.MIPStarRE.LDT.Distribution.map] using
    (Finset.sum_fiberwise_of_maps_to
      (s := 𝒟.support) (t := 𝒟.support.image e) (g := e)
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) 𝒟.weight)
