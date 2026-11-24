-- Prove2me | solution 1 for GlobalTheory.PhiPull.units_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:53.853852+00:00
-- url     : https://prove2.me/submissions/9857a56f-bdd0-42de-831f-5ad6465c0fe9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Theorems.Thm_GlobalTheory_PhiPull_cubN_rel

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
theorem _root_.solution (k : ℕ) (a m x : A) (g n : U) :
    Ω (x * m) ^ ((k : ℤ) - 1) * Ω (a * (x * m)) * (Ω a)⁻¹ * Ω 1 *
      (cubN θ k (β a) (β m) (β x) * (θ (β a) (β x) (β m))⁻¹ *
        ((Ω (a * m))⁻¹ * Ω a * Ω m * (Ω 1)⁻¹ * g * (Ω 1 ^ (k : ℤ) * Ω m ^ (-(k : ℤ)) * n))) =
    Ω x ^ ((k : ℤ) - 1) * Ω (a * m ^ k * x) * (Ω (a * m ^ k))⁻¹ * Ω 1 *
      (cubN θ' k a m x * (θ' a x m)⁻¹ * (g * n)) := by
  rw [cubN_rel β Ω h, h, ← _root_.mul_assoc a x m, mul_comm m x]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module
end GlobalTheory.PhiPull
