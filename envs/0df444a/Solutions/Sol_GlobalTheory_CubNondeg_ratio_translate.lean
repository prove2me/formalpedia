-- Prove2me | solution 1 for GlobalTheory.CubNondeg.ratio_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:18:47.248161+00:00
-- url     : https://prove2.me/submissions/515489a4-eb52-477e-a2c0-97beb4f5ee2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TorsionInvariantDescendsFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RatioTranslate
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_UU_cubN_mul_left
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CubNondeg
namespace GlobalTheory.CubNondeg
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (n : ℕ)
    (x a y : A) (hx : x ^ n = 1) (hy : y ^ n = 1) (e : cubN θ n 1 x y = cubN θ n 1 y x) :
    cubN θ n 1 (a * y) x * (cubN θ n 1 x (a * y))⁻¹ = cubN θ n 1 a x * (cubN θ n 1 x a)⁻¹ := by
  have e₁ := GlobalTheory.UU.cubN_mul_left h n a y x
  have e₂ := h.N_add n 1 x a y
  rw [hy, h.face₂, _root_.one_mul] at e₁
  rw [hx, _root_.mul_one, h.face, _root_.one_mul, _root_.mul_one, h.s01 x, h.s12 a x] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ - a₂ - a₃
end GlobalTheory.CubNondeg
