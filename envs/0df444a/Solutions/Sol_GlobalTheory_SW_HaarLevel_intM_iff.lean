-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.intM_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:51.304817+00:00
-- url     : https://prove2.me/submissions/1811dae0-0539-4605-875b-3bf4144ce678

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
omit [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution (x : Matrix κ ι K) : IntM x ↔ ∃ y, incl K κ ι y = x := by
  constructor
  · intro h
    exact ⟨fun k i => ⟨x k i, h k i⟩, rfl⟩
  · rintro ⟨y, rfl⟩ k i
    exact (y k i).2
end GlobalTheory.SW.HaarLevel
