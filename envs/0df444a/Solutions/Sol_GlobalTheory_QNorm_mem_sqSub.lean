-- Prove2me | solution 1 for GlobalTheory.QNorm.mem_sqSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:50.053629+00:00
-- url     : https://prove2.me/submissions/e8ce09b7-ce4b-46f1-9cd9-37914375e799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L : Type} [Field F] [Field L] (φ : F →+* L) (x : Fˣ) :
    x ∈ sqSub φ ↔ IsSquare (φ (x : F)) := Iff.rfl
end GlobalTheory.QNorm
