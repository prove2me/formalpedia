-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordAtIdeal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:15.800906+00:00
-- url     : https://prove2.me/submissions/1f287193-b487-466e-ad55-7d6571428704

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_spanSingleton_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordAtIdeal W v (f * g) = ordAtIdeal W v f + ordAtIdeal W v g := by
  rw [ordAtIdeal, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul _ _ (spanSingleton_ne_zero W hf) (spanSingleton_ne_zero W hg)]
  rfl
end GroundTheory.Arith.Abelian
