-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isClosed_support_of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:10.943728+00:00
-- url     : https://prove2.me/submissions/cd6c2353-f007-4b21-b2f6-c875a21c77bf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {f : X → ℂ} (hf : IsLocallyConstant f) :
    IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by
    ext x
    simp [Function.mem_support]
  rw [this]
  exact (hf.isOpen_fiber 0).isClosed_compl
end GroundTheory.Automorphic.Whittaker
