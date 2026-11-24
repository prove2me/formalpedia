-- Prove2me | solution 1 for GlobalTheory.SgGlob.form_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:48.904086+00:00
-- url     : https://prove2.me/submissions/4fb9e52d-fb72-408c-beff-b5d8591e6eec

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
theorem _root_.solution {γ : Matrix (Fin n) (Fin n) E} (h : IsUn σ J γ) (v w : Fin n → E) :
    form σ J (γ *ᵥ v) (γ *ᵥ w) = form σ J v w := by
  have e : (fun i => σ ((γ *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* cT σ γ := by
    ext i
    simp [cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [form, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, form]
end GlobalTheory.SgGlob
