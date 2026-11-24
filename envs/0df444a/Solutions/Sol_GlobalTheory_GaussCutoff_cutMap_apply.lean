-- Prove2me | solution 1 for GlobalTheory.GaussCutoff.cutMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:10:00.284507+00:00
-- url     : https://prove2.me/submissions/b7052c05-a247-47f0-9323-dbe245b4b862

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap
noncomputable section
open GlobalTheory GlobalTheory.GaussCutoff
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GlobalTheory.GaussCutoff
theorem _root_.solution (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) (y : E) :
    cutMap h c hc y = cutErr c y * h y := rfl
end GlobalTheory.GaussCutoff
