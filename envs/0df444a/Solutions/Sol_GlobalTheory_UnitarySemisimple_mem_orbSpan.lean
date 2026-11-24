-- Prove2me | solution 1 for GlobalTheory.UnitarySemisimple.mem_orbSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:18.019104+00:00
-- url     : https://prove2.me/submissions/2713ef2f-a9e1-4603-9684-a21a5a121e8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.UnitarySemisimple
theorem _root_.solution (ρ : Representation ℂ H W) (y : W) : y ∈ (orbSpan ρ y).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩
end GlobalTheory.UnitarySemisimple
