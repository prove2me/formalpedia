-- Prove2me | solution 1 for GlobalTheory.QkShift.cubN_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:45:03.853582+00:00
-- url     : https://prove2.me/submissions/440646c3-0246-44ea-a6be-d8caa380ea5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsShiftGen

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
theorem _root_.solution (k : ℕ) (b m x : A) :
    cubN θ k 1 (b * m) x * θ m b x ^ k = θ (m ^ k) (b ^ k) x * cubN θ k 1 b x * cubN θ k 1 m x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c₁ := h.coc (b ^ k * m ^ k) m b x
    have c₂ := h.coc (b ^ k) (m ^ k) m x
    have c₃ := h.coc (m ^ k * m) (b ^ k) b x
    rw [mul_comm m b] at c₁
    rw [h.s01 (b ^ k) (m ^ k), h.s01 (b ^ k) (m ^ k * m)] at c₂
    rw [mul_comm (m ^ k * m) (b ^ k), ← _root_.mul_assoc] at c₃
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [mul_pow b m k, pow_succ m, pow_succ b, pow_succ (θ m b x)]
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₀ := E ih; have a₁ := E c₁; have a₂ := E c₂; have a₃ := E c₃
    simp only [ofMul_mul] at a₀ a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₀ - a₁ + a₂ + a₃
end GlobalTheory.QkShift
