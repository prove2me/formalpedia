-- Prove2me | solution 1 for GlobalTheory.LevDesc.IsRightAct.subRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:44.89498+00:00
-- url     : https://prove2.me/submissions/d2d70eda-aa52-4f67-ab72-d61c5f672d87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)
namespace GlobalTheory.LevDesc
namespace IsRightAct
theorem _root_.solution {st : G → R →ₐ[K] R} (hs : IsRightAct st) (C : Submodule K R)
    (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (g : G) (x : C) : (hs.subRep C hC g x : R) = st g⁻¹ x := rfl
end IsRightAct
end GlobalTheory.LevDesc
