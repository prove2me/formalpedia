-- Prove2me | solution 1 for GlobalTheory.QkPairing.cub_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:45:02.195813+00:00
-- url     : https://prove2.me/submissions/35405b84-45ce-409d-9682-295da4a14418

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_WeilQkPairingExistsUniqueTorus
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.QkPairing
namespace GlobalTheory.QkPairing
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ) (a m b x : A)
    (Sa Sy Say τa τy τay ζ : U) (h₁ : Say * θ a (m ^ k) b = Sa * Sy) (h₂ : τay * θ a (b ^ k) m = τa * τy)
    (h₃ : τy * cubN θ k 1 b m = ζ * (Sy * cubN θ k 1 m b)) :
    cubN θ k a b (x * m) * (θ a (x * m) b)⁻¹ * Sa * (cubN θ k (a * b ^ k) m x * (θ (a * b ^ k) x m)⁻¹ * τay) =
      ζ * (cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * τa * (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * Say)) := by
  have e₀ := h.N_split k a m b
  have e₁ := h.N_add k a m x b
  have e₂ := h.N_add k a b x m
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k (a * b ^ k) m x
  have e₅ := h.N_split k a m x
  have e₆ := h.N_split k a b x
  have e₇ := h.N_split k a b m
  have e₈ := h.coc a (m ^ k) (b ^ k) x
  have e₉ := h.coc a (b ^ k) (m ^ k) x
  rw [mul_comm (b ^ k), h.s01 (b ^ k)] at e₉
  have f₁ := h.coc x b m a
  have f₂ := h.coc x m b a
  rw [mul_comm m b, h.s01 m b a] at f₂
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b] at f₁
  rw [h.s12 (x * m), h.s01 (x * m), h.s12 x m a, h.s01 x a m] at f₂
  have f₃ : θ b x m = θ m x b := by rw [h.s01 b, h.s12 x, h.s01 x]
  rw [f₃] at e₂
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have a₈ := E e₈; have a₉ := E e₉; have b₁ := E f₁; have b₂ := E f₂
  have c₁ := E h₁; have c₂ := E h₂; have c₃ := E h₃
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) -(a₁ - a₂ + a₃ - a₄ + a₅ - a₆ - a₇ + a₈ - a₉ - b₁ + b₂ + c₁ - c₂ - c₃ + a₀)
end GlobalTheory.QkPairing
