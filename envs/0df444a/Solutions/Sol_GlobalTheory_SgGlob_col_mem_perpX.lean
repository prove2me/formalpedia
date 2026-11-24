-- Prove2me | solution 1 for GlobalTheory.SgGlob.col_mem_perpX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:04.417453+00:00
-- url     : https://prove2.me/submissions/6eaf2ff1-23dc-4551-9662-8e22ff75b58b

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
theorem _root_.solution {T : E} {P : Matrix (Fin n) (Fin (r + 1)) E} (h : IsFrame σ J T P)
    (b : Fin (r + 1)) : (fun i => P i b) ∈ perpX σ J P := by
  rw [mem_perpX_iff_form]
  intro a
  have h1 := congrFun (congrFun h.2 a.castSucc) b
  rw [pairM, Matrix.mul_assoc] at h1
  refine h1.trans ?_
  simp [TF, Matrix.diagonal_apply, (Fin.castSucc_lt_last a).ne]
end GlobalTheory.SgGlob
