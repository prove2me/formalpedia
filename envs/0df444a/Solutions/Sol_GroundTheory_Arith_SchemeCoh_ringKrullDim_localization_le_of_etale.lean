-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ringKrullDim_localization_le_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:59.568122+00:00
-- url     : https://prove2.me/submissions/ed7fdf49-ceba-485f-be6a-8cddf17c9240

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve

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
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (Localization.AtPrime (Q.under P)) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  have h : (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact hmap
  calc ringKrullDim (Localization.AtPrime Q)
      ≤ (maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
        ringKrullDim_le_spanFinrank_maximalIdeal _
    _ ≤ (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
        rw [← h]
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _
          (maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
    _ = ringKrullDim (Localization.AtPrime p) :=
        (isRegularLocalRing_iff (Localization.AtPrime p)).mp inferInstance
end GroundTheory.Arith.SchemeCoh
