-- Prove2me | solution 1 for GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:44.478826+00:00
-- url     : https://prove2.me/submissions/33d07e35-872a-4127-93d6-807d1d6c9825

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuadraticUnramifiedIffInertOrSplit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuadraticUnramifiedIffInertOrSplitStatement
import Theorems.Thm_GlobalTheory_quadratic_unramified_iff_inert_or_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ v : HeightOneSpectrum (𝓞 F), ((∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal) ↔ ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime ∨ (v.asIdeal.primesOver (𝓞 E)).ncard = 2)) := by
  first | exact @GlobalTheory.quadratic_unramified_iff_inert_or_split | exact GlobalTheory.quadratic_unramified_iff_inert_or_split | (intros; apply GlobalTheory.quadratic_unramified_iff_inert_or_split <;> assumption)
end _root_.GlobalTheory.T
