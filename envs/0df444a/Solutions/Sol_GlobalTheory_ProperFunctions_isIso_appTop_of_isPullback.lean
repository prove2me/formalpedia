-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:34.153686+00:00
-- url     : https://prove2.me/submissions/b833faf8-f59b-4fe8-a1b0-fe45c7bebb82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isPushout_appTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [QuasiCompact p] [QuasiSeparated p] [IsIso p.appTop] : IsIso q.appTop :=
  (isPushout_appTop H).isIso_inr_of_isIso
end GlobalTheory.ProperFunctions
