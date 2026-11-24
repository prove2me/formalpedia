-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:05.041025+00:00
-- url     : https://prove2.me/submissions/5e17cbaa-508d-4656-95b7-20f04502def8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair

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
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (c : 𝓞 E) (x : E) : c • x = algebraMap (𝓞 E) E c * x := Algebra.smul_def c x
end GlobalTheory.SgGlob.Inhab
