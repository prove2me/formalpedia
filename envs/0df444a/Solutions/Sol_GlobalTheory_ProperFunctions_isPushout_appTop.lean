-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isPushout_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:25.504964+00:00
-- url     : https://prove2.me/submissions/e2223465-718c-43cf-827e-f77796b2e82d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_appLE_top_top

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
    [QuasiCompact p] [QuasiSeparated p] :
    IsPushout p.appTop f.appTop g.appTop q.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace p).mp inferInstance
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤) (UX := ⊤)
    (UY := ⊤) (le_preimage_top f ⊤) (le_preimage_top p ⊤) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top T)
    (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ)
  simpa only [appLE_top_top] using (isIso_pushoutSection_iff ..).mp this
end GlobalTheory.ProperFunctions
