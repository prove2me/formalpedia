-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.index_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:04.880458+00:00
-- url     : https://prove2.me/submissions/f836e017-8ec3-4e2a-99f0-6c5139b21a4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution (R : ℕ) : (nsmulAddMonoidHom R : Matrix κ ι (𝓞 K) →+ _).range.index =
    R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [AddSubgroup.index_range_nsmul, Module.finrank_matrix, RingOfIntegers.rank]
  ring
end GlobalTheory.SW.HaarLevel
