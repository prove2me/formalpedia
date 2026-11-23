-- Prove2me | solution 1 for GlobalTheory.BSP.denseRange_ofPre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:03.148829+00:00
-- url     : https://prove2.me/submissions/6d69d34c-84ba-46a7-96b3-410c136f642a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open GlobalTheory GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
namespace GlobalTheory.BSP
namespace _root_.GlobalTheory.BSP
theorem _root_.solution :
    DenseRange (_root_.GlobalTheory.BSP.ofPre l u ρ) :=
  UniformSpace.Completion.denseRange_coe
end _root_.GlobalTheory.BSP
end GlobalTheory.BSP
