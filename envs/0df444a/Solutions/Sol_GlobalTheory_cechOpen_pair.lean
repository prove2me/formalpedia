-- Prove2me | solution 1 for GlobalTheory.cechOpen_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:17.793352+00:00
-- url     : https://prove2.me/submissions/66e7c080-e9ea-4cbe-9a23-8ad309b09f0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace Opposite
universe w v u
noncomputable section
open GlobalTheory
variable {T : Type w} [TopologicalSpace T] {ι κ : Type}
variable (V : Opens T) (U : ι → Opens T)
namespace GlobalTheory
theorem _root_.solution [DecidableEq ι] (i j : ι) : cechOpen V U {i, j} = V ⊓ (U i ⊓ U j) := by
  rw [cechOpen_insert, cechOpen_singleton, inf_left_comm]
end GlobalTheory
