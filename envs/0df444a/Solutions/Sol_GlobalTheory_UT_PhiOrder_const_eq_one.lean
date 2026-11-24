-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.const_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:00.095192+00:00
-- url     : https://prove2.me/submissions/bcca49e6-c8a0-4321-b07a-cc2d44deee8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
import Theorems.Thm_GlobalTheory_UT_PhiOrder_pot_zero
import Theorems.Thm_GlobalTheory_UT_PhiOrder_pot_one
import Theorems.Thm_GlobalTheory_UT_PhiOrder_cub_eq_pot
import Theorems.Thm_GlobalTheory_UT_PhiOrder_cubN_eq_pot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.UT.PhiOrder
theorem _root_.solution (h : IsCub θ) (b : A) (m k : ℕ) (hk : k = 2 * m + 1) (S : ℕ → U) (s w ψ ρ τ E : U)
    (hS : ∀ i, S i * cubN θ i 1 (b ^ k) b = s ^ i) (hτ : τ * cubN θ k 1 b (b ^ k) = s ^ k)
    (hE : τ = E * ψ ^ 2 * ρ ^ 2)
    (hw : w ^ k * ((E * pot θ b (2 * k)) ^ m * (pot θ b k ^ (k + 2 * m))⁻¹) = ψ * ρ) :
    (∏ i ∈ Finset.range k, H1.hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (S i * w)) * (ψ ^ k * ρ ^ k)⁻¹ = 1 := by
  set P : ℕ → Additive U := fun n => Additive.ofMul (pot θ b n) with hP
  have P0 : P 0 = 0 := pot_zero b
  have P1 : P 1 = 0 := pot_one b
  have cN : ∀ n a c x, Additive.ofMul (cubN θ n (b ^ a) (b ^ c) (b ^ x)) = P (a + c * n + x) - P (a + x) - P (a + c * n) +
    P a - n • (P (c + x) - P c - P x) := cubN_eq_pot h b
  have cT : ∀ i j l, Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) =
    P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l := cub_eq_pot h b
  let f : ℕ → Additive U := fun i => P (k * i + (k - i)) + k • P (k - i) - P (k - i) - P (k * i)
  let d : Additive U := Additive.ofMul s + P (k + 1) - P k
  have term : ∀ i ∈ Finset.range k, Additive.ofMul (H1.hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (S i * w)) =
      (f (i + 1) - f i) + (i • d + Additive.ofMul w) := by
    intro i hi
    obtain ⟨x, hx⟩ : ∃ x, k = i + 1 + x := ⟨k - (i + 1), by have := Finset.mem_range.1 hi; omega⟩
    have x₁ : k - 1 - i = x := by omega
    have x₂ : k - (i + 1) = x := by omega
    have x₃ : k - i = 1 + x := by omega
    have a₁ := cN k (k * i) 1 x
    have a₂ := cT (k * i) x 1
    have a₃ := cN i 0 k 1
    have a₄ := congrArg Additive.ofMul (hS i)
    rw [pow_one] at a₁ a₂ a₃
    rw [pow_zero, zero_add, zero_add, P0, P1] at a₃
    rw [_root_.one_mul, P1, ← Nat.mul_succ] at a₁
    rw [P1, add_assoc (k * i), add_comm x 1] at a₂
    rw [ofMul_mul, a₃, ofMul_pow] at a₄
    simp only [f, d, H1.hv, ofMul_mul, ofMul_inv, x₁, x₂, x₃, ← pow_mul, a₁, a₂, Nat.succ_eq_add_one]
    linear_combination (norm := module) a₄
  have gauss : ∑ i ∈ Finset.range k, i = m * k := by
    have := Finset.sum_range_id_mul_two k
    rw [show k - 1 = 2 * m by omega] at this
    nlinarith
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_prod, Finset.sum_congr rfl term, Finset.sum_add_distrib, Finset.sum_range_sub,
    Finset.sum_add_distrib, Finset.sum_nsmul_assoc, gauss, Finset.sum_const, Finset.card_range]
  have a₁ := cN k 0 1 k
  rw [pow_zero, pow_one, zero_add, zero_add, _root_.one_mul, ← two_mul, add_comm 1 k, P0, P1] at a₁
  have a₂ := congrArg Additive.ofMul hτ
  have a₃ := congrArg Additive.ofMul hw
  rw [ofMul_mul, a₁, hE] at a₂
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one, f, d, Nat.sub_self, add_zero, mul_zero, zero_add, Nat.sub_zero,
    P0] at a₂ a₃ ⊢
  change k • _ + (m • (_ + P (2 * k)) + -((k + 2 * m) • P k)) = _ at a₃
  subst hk
  linear_combination (norm := module) a₃ - m • a₂
end GlobalTheory.UT.PhiOrder
