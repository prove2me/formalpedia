-- Prove2me | solution 1 for GlobalTheory.SgGlob.UO.entry_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.051408+00:00
-- url     : https://prove2.me/submissions/ff4676ad-72df-400a-a337-f421bec2d736

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
variable {n r : ℕ}
namespace GlobalTheory.SgGlob
namespace UO
theorem _root_.solution {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hu : u ∈ UO E r) (a b : Fin (r + 1)) :
    u a b ∈ dInv E ((b : ℕ) - a) := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact hu.2 a b h
  · rw [(hu.1 a a).2 rfl, Nat.sub_self, dInv, pow_zero]
    exact FractionalIdeal.one_mem_one _
  · rw [(hu.1 a b).1 h]
    exact FractionalIdeal.zero_mem _
end UO
end GlobalTheory.SgGlob
