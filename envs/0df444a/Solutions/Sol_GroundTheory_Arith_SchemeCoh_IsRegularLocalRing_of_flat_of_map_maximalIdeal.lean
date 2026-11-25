-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:34.850571+00:00
-- url     : https://prove2.me/submissions/6bbbf081-78d4-4ae9-9c43-ebd20656998d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ringKrullDim_le_of_hasGoingDown

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
namespace GroundTheory.Arith.SchemeCoh
namespace IsRegularLocalRing
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [IsRegularLocalRing A]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) : IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← h]
  calc (((maximalIdeal A).map (algebraMap A B)).spanFinrank : WithBot ℕ∞)
      ≤ (maximalIdeal A).spanFinrank := by
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal A).fg_of_isNoetherianRing
    _ = ringKrullDim A := (isRegularLocalRing_iff A).mp inferInstance
    _ ≤ ringKrullDim B := ringKrullDim_le_of_hasGoingDown
end IsRegularLocalRing
end GroundTheory.Arith.SchemeCoh
