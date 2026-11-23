-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.mem_perSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:06.939888+00:00
-- url     : https://prove2.me/submissions/fec0af30-0525-4111-bf4a-b472da152d06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_perSub_eq_range

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
theorem _root_.solution (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, R • incl K κ ι y = x := by
  rw [perSub_eq_range]
  simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply, nsmulAddMonoidHom_apply, map_nsmul]
end GlobalTheory.SW.HaarLevel
