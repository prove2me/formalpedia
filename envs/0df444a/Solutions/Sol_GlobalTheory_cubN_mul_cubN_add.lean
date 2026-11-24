-- Prove2me | solution 1 for GlobalTheory.cubN_mul_cubN_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:59.517821+00:00
-- url     : https://prove2.me/submissions/9ae0e762-3e98-4580-a462-b14f1d54bf78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TranslationUnitMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (k l : ℕ) (b c m y : A) :
    cubN θ k b m y * cubN θ l c m y * θ (b * m ^ k) (c * m ^ l) y = cubN θ (k + l) (b * c) m y * θ b c y := by
  induction k with
  | zero =>
    induction l with
    | zero => simp [cubN]
    | succ l ih =>
      have e := h.coc b (c * m ^ l) m y
      simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, Nat.zero_add, pow_zero, _root_.mul_one,
        _root_.one_mul] at ih ⊢
      rw [pow_succ m, ← _root_.mul_assoc c, _root_.mul_assoc b c]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have e' := congrArg Additive.ofMul e
      simp only [_root_.mul_assoc b c] at ih'
      simp only [ofMul_mul, _root_.mul_assoc b c] at ih' e' ⊢
      linear_combination (norm := abel) ih' - e'
  | succ k ih =>
    have e := h.coc m (b * m ^ k) (c * m ^ l) y
    have p₁ : m * (b * m ^ k) = b * m ^ (k + 1) := by rw [pow_succ, mul_comm m, _root_.mul_assoc]
    have p₂ : b * m ^ k * (c * m ^ l) = b * c * m ^ (k + l) := by rw [pow_add, _root_.mul_mul_mul_comm]
    rw [p₁, p₂, h.s01 m, h.s01 m] at e
    rw [Nat.add_right_comm]
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at ih' e' ⊢
    linear_combination (norm := abel) ih' + e'
end GlobalTheory
