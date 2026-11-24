-- Prove2me | solution 1 for GlobalTheory.PairingLevels.comm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:55.684949+00:00
-- url     : https://prove2.me/submissions/fe92e39e-19c3-4cf0-bc5c-f6f2cd96c966

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
namespace GlobalTheory.PairingLevels
theorem _root_.solution {B U : Type} [CommGroup B] [CommGroup U] (v : B → B → B → U) (φ φ' ψ χ : B → U) (k : ℤ) (l : ℕ)
    (x y : B) (hv : ∀ a, v a x 1 * v a y x = v a y 1 * v a x y)
    (hA : ∀ w, φ (w * x) * φ 1 * v w y x ^ k = φ w * φ x * v w y 1 ^ k)
    (hB : χ y * ψ 1 * (∏ i ∈ Finset.range l, v (x ^ i) x 1) ^ k =
      χ 1 * ψ y * (∏ i ∈ Finset.range l, v (x ^ i) x y) ^ k)
    (hC : φ' x * φ 1 ^ l = φ' 1 * φ x ^ l) :
    χ 1 * φ' x * (φ' 1 * χ y)⁻¹ = ψ 1 * φ (x ^ l) * (φ 1 * ψ y)⁻¹ := by
  have key : ∀ n : ℕ, φ (x ^ n) * φ 1 ^ n * (∏ i ∈ Finset.range n, v (x ^ i) x y) ^ k =
      φ 1 * φ x ^ n * (∏ i ∈ Finset.range n, v (x ^ i) x 1) ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have a := congrArg Additive.ofMul (hA (x ^ n))
      have b := congrArg Additive.ofMul (hv (x ^ n))
      have c := congrArg Additive.ofMul ih
      rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow] at a b c ⊢
      linear_combination (norm := module) a + c - k • b
  have a := congrArg Additive.ofMul (key l)
  have b := congrArg Additive.ofMul hB
  have c := congrArg Additive.ofMul hC
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv] at a b c ⊢
  linear_combination (norm := module) c - a - b
end GlobalTheory.PairingLevels
