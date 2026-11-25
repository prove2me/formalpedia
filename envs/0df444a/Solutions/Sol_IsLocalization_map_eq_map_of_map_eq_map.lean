-- Prove2me | solution 1 for IsLocalization.map_eq_map_of_map_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:47.735798+00:00
-- url     : https://prove2.me/submissions/42b310ff-2787-47cf-8693-cef81a61785d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalization
namespace IsLocalization
theorem _root_.solution {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M : Submonoid R) [IsLocalization M S]
    [IsLocalization M T] {I J : Ideal R}
    (h : Ideal.map (algebraMap R S) I = Ideal.map (algebraMap R S) J) :
    Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J := by
  have he : ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom).comp (algebraMap R S)
      = algebraMap R T :=
    RingHom.ext fun r => by
      show (IsLocalization.algEquiv M S T) (algebraMap R S r) = algebraMap R T r
      exact (IsLocalization.algEquiv M S T).commutes r
  have hmap : ∀ K : Ideal R, Ideal.map (algebraMap R T) K =
      Ideal.map ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom)
        (Ideal.map (algebraMap R S) K) := by
    intro K
    rw [Ideal.map_map, he]
  rw [hmap, hmap, h]
end IsLocalization
