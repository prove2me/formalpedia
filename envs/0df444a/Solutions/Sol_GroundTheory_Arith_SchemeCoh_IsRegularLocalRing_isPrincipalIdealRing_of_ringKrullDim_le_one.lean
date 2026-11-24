-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:38.985541+00:00
-- url     : https://prove2.me/submissions/3356eb27-ac0b-44f3-968e-8ce70b1e1364

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain


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
theorem _root_.solution {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R := by
  have : IsDomain R := IsRegularLocalRing.isDomain
  have hreg := (isRegularLocalRing_iff R).mp inferInstance
  have hle : (maximalIdeal R).spanFinrank ≤ 1 := by
    rw [← hreg] at h; exact_mod_cast h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · have hbot : maximalIdeal R = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have : IsDiscreteValuationRing R := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp (by
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; exact h1)
    infer_instance
end IsRegularLocalRing
end GroundTheory.Arith.SchemeCoh
