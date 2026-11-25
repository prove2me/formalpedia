-- Prove2me | solution 1 for GlobalTheory.T.exists_common_unramified_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:55.77906+00:00
-- url     : https://prove2.me/submissions/c40e2bc3-86ea-4a94-918c-be96784462b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCommonUnramifiedExtension
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCommonUnramifiedExtensionStatement
import Theorems.Thm_GlobalTheory_compositum_finite_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by
  first | exact @GlobalTheory.compositum_finite_formallyUnramified | exact GlobalTheory.compositum_finite_formallyUnramified | (intros; apply GlobalTheory.compositum_finite_formallyUnramified <;> assumption)
end _root_.GlobalTheory.T
