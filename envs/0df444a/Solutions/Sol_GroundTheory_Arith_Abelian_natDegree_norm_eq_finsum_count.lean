-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.natDegree_norm_eq_finsum_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:33.852991+00:00
-- url     : https://prove2.me/submissions/610618e1-29cf-4f4e-b406-0ce67675930f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_eq_finsum_count_of_relNorm_eq

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
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {f : W.toAffine.CoordinateRing} (hf : f ≠ 0) :
    ((Algebra.norm F[X] f).natDegree : ℤ) = ∑ᶠ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      FractionalIdeal.count W.toAffine.FunctionField v
        ((Ideal.span {f} : Ideal _) :
          FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField) := by
  refine natDegree_eq_finsum_count_of_relNorm_eq W ?_ ?_
  · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  · rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm]
end GroundTheory.Arith.Abelian
