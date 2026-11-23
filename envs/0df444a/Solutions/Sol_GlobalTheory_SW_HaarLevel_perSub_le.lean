-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.perSub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:54.807008+00:00
-- url     : https://prove2.me/submissions/72ebfe1f-700a-4e7b-9f97-cca503f6e726

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub

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
omit [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution (R S : ℕ) : perSub K κ ι (R * S) ≤ perSub K κ ι R := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_perSub _ _).1 hx
  exact (mem_perSub _ _).2 ⟨S • y, by rw [map_nsmul, mul_smul]⟩
end GlobalTheory.SW.HaarLevel
