-- Prove2me | solution 1 for GlobalTheory.SW.isSB_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:00.619474+00:00
-- url     : https://prove2.me/submissions/e55a8cb1-c746-42b2-9e99-dcdadb0791b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW
theorem _root_.solution : IsSB (0 : Matrix κ ι K → ℂ) := by
  refine ⟨1, Nat.one_pos, fun x hx => ?_, fun x y _ => rfl⟩
  exact absurd rfl hx
end GlobalTheory.SW
