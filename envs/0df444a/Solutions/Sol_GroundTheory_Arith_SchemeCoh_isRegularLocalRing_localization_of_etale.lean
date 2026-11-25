-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:23.007809+00:00
-- url     : https://prove2.me/submissions/0701d22b-cba0-40ad-ad6f-365b92cc1017

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_of_flat_of_map_maximalIdeal

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
theorem _root_.solution {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  apply IsRegularLocalRing.of_flat_of_map_maximalIdeal (A := Localization.AtPrime p)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
  exact hmap
end GroundTheory.Arith.SchemeCoh
