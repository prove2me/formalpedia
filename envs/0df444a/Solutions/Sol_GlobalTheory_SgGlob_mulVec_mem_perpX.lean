-- Prove2me | solution 1 for GlobalTheory.SgGlob.mulVec_mem_perpX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:12.302804+00:00
-- url     : https://prove2.me/submissions/9dddc7f6-f8df-4627-a25a-70f4ad523ed3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Theorems.Thm_GlobalTheory_SgGlob_form_mulVec

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
theorem _root_.solution {γ : Matrix (Fin n) (Fin n) E} (h : IsUn σ J γ)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    γ *ᵥ v ∈ perpX σ J (γ * P) ↔ v ∈ perpX σ J P := by
  simp only [mem_perpX_iff_form]
  refine forall_congr' fun a => ?_
  rw [← form_mulVec h v]
  rfl
end GlobalTheory.SgGlob
