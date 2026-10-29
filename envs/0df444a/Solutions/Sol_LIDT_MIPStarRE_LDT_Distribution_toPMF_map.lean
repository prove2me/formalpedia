-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Distribution.toPMF_map
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:23.06912+00:00
-- url     : https://prove2.me/submissions/4044062e-cc2c-499c-9e15-e86e5c521477

-- Generated proof for MIPStarRE.LDT.Distribution.toPMF_map.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map

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
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (h𝒟 : 𝒟.IsProbability) (e : α → β) :
    (𝒟.map e).toPMF (h𝒟.map e) = (𝒟.toPMF h𝒟).map e := by
  classical
  ext b
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.toPMF_apply, PMF.map_apply, _root_.LIDT.MIPStarRE.LDT.Distribution.map_weight]
  rw [ENNReal.ofReal_sum_of_nonneg
    (s := 𝒟.support.filter (fun a => e a = b))
    (fun a _ => 𝒟.nonnegative a)]
  rw [tsum_eq_sum (s := 𝒟.support)]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro a ha
    by_cases hea : e a = b
    · have hba : b = e a := hea.symm
      rw [if_pos hea, if_pos hba, _root_.LIDT.MIPStarRE.LDT.Distribution.toPMF_apply]
    · have hba : b ≠ e a := fun hba => hea hba.symm
      rw [if_neg hea, if_neg hba]
  · intro a ha
    by_cases hba : b = e a
    · rw [if_pos hba, _root_.LIDT.MIPStarRE.LDT.Distribution.toPMF_apply_of_notMem 𝒟 h𝒟 ha]
    · rw [if_neg hba]
