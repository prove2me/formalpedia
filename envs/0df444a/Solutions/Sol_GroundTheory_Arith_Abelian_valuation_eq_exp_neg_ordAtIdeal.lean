-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuation_eq_exp_neg_ordAtIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:34.203012+00:00
-- url     : https://prove2.me/submissions/1a4895c0-bfae-44ae-9df7-503ee457a97a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_ordAtIdeal_mul
import Theorems.Thm_GroundTheory_Arith_Abelian_ordAtIdeal_algebraMap
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
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    v.valuation W.toAffine.FunctionField f = exp (-ordAtIdeal W v f) := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only at hf ⊢
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf (IsLocalization.mk'_zero _)
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hs' : algebraMap _ W.toAffine.FunctionField (s : W.toAffine.CoordinateRing) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ W.toAffine.FunctionField)).mpr hs
  have hsa : Ideal.span {a} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hss : Ideal.span {(s : W.toAffine.CoordinateRing)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hord := ordAtIdeal_mul W v hf hs'
  rw [IsLocalization.mk'_spec, ordAtIdeal_algebraMap, ordAtIdeal_algebraMap] at hord
  rw [HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.intValuation_if_neg _ ha,
    HeightOneSpectrum.intValuation_if_neg _ hs, ← FractionalIdeal.count_coe W.toAffine.FunctionField v hsa,
    ← FractionalIdeal.count_coe W.toAffine.FunctionField v hss, ← exp_sub]
  congr 1
  linarith
end GroundTheory.Arith.Abelian
