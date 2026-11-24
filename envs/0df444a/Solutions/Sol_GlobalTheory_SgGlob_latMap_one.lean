-- Prove2me | solution 1 for GlobalTheory.SgGlob.latMap_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:11.448144+00:00
-- url     : https://prove2.me/submissions/6f02b11b-a97c-4ef9-bee4-90a4c4e35fa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_mem_latMap

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
namespace GlobalTheory.SgGlob
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext v
  simp [mem_latMap]
end GlobalTheory.SgGlob
