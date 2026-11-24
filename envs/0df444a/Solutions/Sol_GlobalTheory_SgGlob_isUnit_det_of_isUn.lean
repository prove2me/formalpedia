-- Prove2me | solution 1 for GlobalTheory.SgGlob.isUnit_det_of_isUn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:48.394799+00:00
-- url     : https://prove2.me/submissions/fcf97ad0-822a-4f35-bfc2-6efe11ca6868

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
theorem _root_.solution {γ : Matrix (Fin n) (Fin n) E} (hJ : IsUnit J.det) (h : IsUn σ J γ) :
    IsUnit γ.det := by
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul] at e
  exact isUnit_of_mul_isUnit_right (e ▸ hJ)
end GlobalTheory.SgGlob
