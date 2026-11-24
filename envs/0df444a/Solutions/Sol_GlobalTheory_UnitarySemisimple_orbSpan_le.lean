-- Prove2me | solution 1 for GlobalTheory.UnitarySemisimple.orbSpan_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:18.667805+00:00
-- url     : https://prove2.me/submissions/cd200d0b-d535-46d1-ad6a-32414c4596cc

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
theorem _root_.solution (ρ : Representation ℂ H W) (y : W) (Z : Subrepresentation ρ)
    (hy : y ∈ Z.toSubmodule) : (orbSpan ρ y).toSubmodule ≤ Z.toSubmodule :=
  Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact Z.apply_mem_toSubmodule g hy)
end GlobalTheory.UnitarySemisimple
