-- Prove2me | solution 1 for IsRegularLocalRing.isRadical_span_singleton_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:10.441668+00:00
-- url     : https://prove2.me/submissions/c88d523b-afe9-46a6-a33f-1c0896c1ce53

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Theorems.Thm_IsRegularLocalRing_isPrime_span_singleton
import Theorems.Thm_IsRegularLocalRing_notMem_span_singleton
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_span_singleton_prod_finset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsRegularLocalRing
open IsLocalRing
universe u
namespace IsRegularLocalRing
theorem _root_.solution {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by
  classical
  exact FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x Finset.univ
    (fun i _ => isPrime_span_singleton x hx hli i)
    (fun i _ j _ hij => notMem_span_singleton x hx hli hij)
end IsRegularLocalRing
