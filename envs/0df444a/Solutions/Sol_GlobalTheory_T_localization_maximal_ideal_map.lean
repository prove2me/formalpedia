-- Prove2me | solution 1 for GlobalTheory.T.localization_maximal_ideal_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:22.869274+00:00
-- url     : https://prove2.me/submissions/7e60646c-3ec6-4d6a-a7fc-7c1df007ea5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationMaximalIdealMap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationMaximalIdealMapStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ (IsLocalRing.maximalIdeal B).map (algebraMap B S) → (IsLocalRing.maximalIdeal B).map (algebraMap B S) ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → (IsLocalRing.maximalIdeal B).map ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  first | exact @GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | exact GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | (intros; apply GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient <;> assumption)
end _root_.GlobalTheory.T
