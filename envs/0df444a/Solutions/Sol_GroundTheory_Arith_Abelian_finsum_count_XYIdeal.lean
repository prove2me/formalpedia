-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.finsum_count_XYIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:32.483802+00:00
-- url     : https://prove2.me/submissions/944da9d5-3bae-4668-af0b-d02531f5348a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Theorems.Thm_GroundTheory_Arith_Abelian_heightOneOfNonsingular_asIdeal
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((XYIdeal W.toAffine x (C y) : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) = 1 := by
  classical
  have hc := fun v => FractionalIdeal.count_maximal W.toAffine.FunctionField v
    (heightOneOfNonsingular h)
  simp only [heightOneOfNonsingular_asIdeal] at hc
  rw [finsum_eq_single _ (heightOneOfNonsingular h) (fun v hv => by
    rw [hc v, if_neg (fun e => hv e.symm)]), hc, if_pos rfl]
end GroundTheory.Arith.Abelian
