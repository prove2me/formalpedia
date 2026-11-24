-- Prove2me | solution 1 for GlobalTheory.PhiPull.cubN_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:27:12.44088+00:00
-- url     : https://prove2.me/submissions/bfead162-029f-4c6d-b19c-055e23e950a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {A B U : Type} [CommGroup A] [CommGroup B] [CommGroup U] {θ : B → B → B → U} {θ' : A → A → A → U}
  (β : A →* B) (Ω : A → U)
  (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a *
      Ω b * Ω c * (Ω 1)⁻¹ * θ' a b c)
include h
namespace GlobalTheory.PhiPull
theorem _root_.solution (k : ℕ) (a m x : A) : cubN θ k (β a) (β m) (β x) =
    Ω (a * m ^ k * x) * (Ω (a * x))⁻¹ * (Ω (a * m ^ k))⁻¹ * Ω a * ((Ω (m * x))⁻¹ * Ω m * Ω x * (Ω 1)⁻¹) ^ k *
      cubN θ' k a m x := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have c := h (a * m ^ k) m x
    rw [map_mul, map_pow] at c
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    rw [ih, c, pow_succ m, ← _root_.mul_assoc a, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end GlobalTheory.PhiPull
