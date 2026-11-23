-- Prove2me | solution 1 for GlobalTheory.bijective_ofRealHom_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:42.539946+00:00
-- url     : https://prove2.me/submissions/734e1827-b772-4265-adda-2c741bf3aa4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
omit [NumberField F]
variable (F)
namespace GlobalTheory
theorem _root_.solution :
    Function.Bijective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ) := by
  refine ⟨fun σ τ h => RingHom.ext fun x => ?_, fun φ => ?_⟩
  · simpa using RingHom.congr_fun h x
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x => by simp⟩
end GlobalTheory
