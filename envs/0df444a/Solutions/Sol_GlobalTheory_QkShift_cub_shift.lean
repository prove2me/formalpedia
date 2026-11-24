-- Prove2me | solution 1 for GlobalTheory.QkShift.cub_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:04:55.039811+00:00
-- url     : https://prove2.me/submissions/9b34d02d-e723-4804-86bf-bd66c3e4186a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsShiftGen
import Theorems.Thm_GlobalTheory_QkShift_cubN_one_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.QkShift
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h
namespace GlobalTheory.QkShift
theorem _root_.solution (k : ℕ) (a m b x : A) (Sa Sm Sam Sq τ P w : U) (h₁ : Sam * cubN θ k a m b = Sa * Sm ^ k)
    (h₂ : Sq * θ a b m = Sa * τ) :
    cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * (τ * P) *
        (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * (Sam * w)) =
      cubN θ k a (b * m) x * (θ a x (b * m))⁻¹ * (Sq * (w * P * Sm ^ k)) := by
  have e₁ := h.N_add k a m x b
  have e₂ := cubN_one_mul h k b m x
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k a (b * m) x
  have e₅ := h.N_split k a m x
  have e₆ := h.coc a (m ^ k) (b ^ k) x
  have e₇ := h.coc x b m a
  rw [h.s12 m x b] at e₁
  rw [← mul_pow, mul_comm m b] at e₆
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b, h.s12 x (b * m), h.s01 x a, h.s12 b m a,
    h.s01 b a m] at e₇
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have c₁ := E h₁; have c₂ := E h₂
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) a₁ - a₂ + a₃ - a₄ + a₅ + a₆ - a₇ + c₁ - c₂
end GlobalTheory.QkShift
