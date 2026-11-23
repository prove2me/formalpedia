-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.embA_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:15.530438+00:00
-- url     : https://prove2.me/submissions/9a52789e-c0ba-42cd-9fc1-a77e51aeb21c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckePoisson
variable {K : Type} [Field K] [NumberField K] {I : Type}
namespace GlobalTheory.HeckePoisson
theorem _root_.solution (φ : I → K →+* ℂ) (α : 𝓞 K) (i : I) : embA φ α i = φ i (α : K) := rfl
end GlobalTheory.HeckePoisson
