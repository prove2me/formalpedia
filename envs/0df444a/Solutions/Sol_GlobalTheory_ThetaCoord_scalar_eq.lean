-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.scalar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:30:03.449215+00:00
-- url     : https://prove2.me/submissions/2885c923-552b-438c-b0fa-b21e9049da21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
namespace GlobalTheory.ThetaCoord
theorem _root_.solution {G U : Type} [CommGroup G] [CommGroup U] (f g e ν : G → U) (X Y : G) (c d : U) (l : ℕ)
    (hY : Y ^ (2 * l + 1) = 1)
    (hf : ∀ m, ∏ j ∈ Finset.range (2 * l + 1), f (X ^ j * m) = 1)
    (hg : ∀ m, ∏ j ∈ Finset.range (2 * l + 1), g (Y ^ j * m) = 1)
    (he : ∀ m, ∏ j ∈ Finset.range (2 * l + 1), e ((Y * X) ^ j * m) = 1)
    (sf : ∀ m, f (X⁻¹ * m) * ν m * (f m⁻¹ * (ν (X⁻¹ * m))⁻¹) = 1)
    (sg : ∀ m, g (Y⁻¹ * m) * ν m * (g m⁻¹ * (ν (Y⁻¹ * m))⁻¹) = 1)
    (se : ∀ m, e ((Y * X)⁻¹ * m) * ν m * (e m⁻¹ * (ν ((Y * X)⁻¹ * m))⁻¹) = 1)
    (hc : ∀ m, f m * g (X * m) = g m * f (Y * m) * c) (hd : ∀ m, f m * g (X * m) = d * e m) :
    d = c ^ (l + 1) := by
  have h₁ : ∀ n m, f m * ∏ j ∈ Finset.range n, g (Y ^ j * (X * m)) =
      (∏ j ∈ Finset.range n, g (Y ^ j * m)) * f (Y ^ n * m) * c ^ n := fun n m => by
    induction n with
    | zero => simp
    | succ n ih =>
      have := hc (Y ^ n * m)
      rw [mul_left_comm X, ← _root_.mul_assoc Y, ← pow_succ'] at this
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ← _root_.mul_assoc, ih, pow_succ c]
      apply Additive.ofMul.injective
      replace this := congrArg Additive.ofMul this
      simp only [ofMul_mul] at this ⊢
      linear_combination (norm := abel) this
  have h₂ : ∀ n m, d ^ n * (∏ j ∈ Finset.range n, e ((Y * X) ^ j * m)) * c ^ (n.choose 2) =
      (∏ j ∈ Finset.range n, f (X ^ j * m)) * ∏ j ∈ Finset.range n, g (Y ^ j * (X ^ n * m)) := fun n m => by
    induction n with
    | zero => simp
    | succ n ih =>
      have a := h₁ n (X ^ n * m)
      have b := hd ((Y * X) ^ n * m)
      have e₁ : X * (X ^ n * m) = X ^ (n + 1) * m := by rw [pow_succ', _root_.mul_assoc]
      have e₂ : X * ((Y * X) ^ n * m) = Y ^ n * (X ^ (n + 1) * m) := by rw [mul_pow, pow_succ']; ac_rfl
      have e₃ : Y ^ n * (X ^ n * m) = (Y * X) ^ n * m := by rw [mul_pow, _root_.mul_assoc]
      rw [e₁, e₃] at a
      rw [e₂] at b
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Nat.choose_succ_succ',
        Nat.choose_one_right, pow_add c, pow_succ d]
      apply Additive.ofMul.injective
      replace a := congrArg Additive.ofMul a
      replace b := congrArg Additive.ofMul b
      replace ih := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a b ih ⊢
      linear_combination (norm := abel) ih - a - b
  have cq : c ^ (2 * l + 1) = 1 := by
    have := h₁ (2 * l + 1) 1
    rw [hg, hg, hY, _root_.one_mul, _root_.one_mul, _root_.mul_one] at this
    exact left_eq_mul.1 this
  have dq : d ^ (2 * l + 1) = 1 := by
    have := h₂ (2 * l + 1) 1
    have e₁ : (2 * l + 1).choose 2 = (2 * l + 1) * l := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
    rwa [he, hf, hg, e₁, pow_mul, cq, one_pow, _root_.mul_one, _root_.mul_one, _root_.mul_one] at this
  have d2 : d ^ 2 = c := by
    have a₁ := sf 1
    have a₂ := sg X⁻¹
    have a₃ := se 1
    have a₄ := hc (Y * X)⁻¹
    have a₅ := hd (Y * X)⁻¹
    have a₆ := hd 1
    have e₁ : Y⁻¹ * X⁻¹ = (Y * X)⁻¹ := (mul_inv _ _).symm
    have e₂ : Y * (Y * X)⁻¹ = X⁻¹ := by rw [mul_inv, mul_inv_cancel_left]
    rw [e₂] at a₄
    rw [e₁] at a₂
    simp only [_root_.mul_one, inv_one, inv_inv] at a₁ a₂ a₃ a₆
    apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    replace a₄ := congrArg Additive.ofMul a₄
    replace a₅ := congrArg Additive.ofMul a₅
    replace a₆ := congrArg Additive.ofMul a₆
    simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_pow] at a₁ a₂ a₃ a₄ a₅ a₆ ⊢
    linear_combination (norm := module) a₁ + a₂ - a₃ + a₄ - a₅ - a₆
  rw [← d2, ← pow_mul, show 2 * (l + 1) = 2 * l + 1 + 1 by ring, pow_succ, dq, _root_.one_mul]
end GlobalTheory.ThetaCoord
