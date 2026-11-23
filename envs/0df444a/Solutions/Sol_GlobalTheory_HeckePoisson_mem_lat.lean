-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:32.861807+00:00
-- url     : https://prove2.me/submissions/2cf34c1d-5445-4611-b47f-8872aad13680

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
theorem _root_.solution {φ : I → K →+* ℂ} {M : Ideal (𝓞 K)} {x : EuclideanSpace ℂ I} :
    x ∈ lat φ M ↔ ∃ μ ∈ M, embA φ μ = x := by
  show x ∈ M.toAddSubgroup.map (embA φ) ↔ _
  rw [AddSubgroup.mem_map]
  rfl
end GlobalTheory.HeckePoisson
