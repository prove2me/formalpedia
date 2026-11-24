-- Prove2me | solution 1 for GlobalTheory.SgGlob.IsRed.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:09.95839+00:00
-- url     : https://prove2.me/submissions/17ce40c1-f69c-4756-9cc9-269dfad25382

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]
namespace GlobalTheory.SgGlob
namespace IsRed
theorem _root_.solution {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E} {x : Lz E m}
    {al : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (y : Fin m → E) :
    y ∈ x.1 ↔ ∃ v ∈ latIn Λ (perpX σ J P), al *ᵥ v = y := by
  rw [← h.2.2.2.1]
  rfl
end IsRed
end GlobalTheory.SgGlob
