-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_add_eq_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:11.70688+00:00
-- url     : https://prove2.me/submissions/ab11e020-b824-40e1-9c1a-d60ef167ba24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Theorems.Thm_GlobalTheory_SqZero_IsAway_mem_map
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
namespace GlobalTheory.SqZero
theorem _root_.solution {T₁ T₂ T₁₂ : Type} [CommRing T₁] [Algebra R T₁] [CommRing T₂]
    [Algebra R T₂] [CommRing T₁₂] [Algebra R T₁₂] {f g : T} (hfg : IsCoprime f g)
    {ρ₁ : T →ₐ[R] T₁} {ρ₂ : T →ₐ[R] T₂} {ρ : T →ₐ[R] T₁₂} (h₁ : IsAway ρ₁ f) (h₂ : IsAway ρ₂ g)
    (h : IsAway ρ (f * g)) {a : T₁ →ₐ[R] T₁₂} {b : T₂ →ₐ[R] T₁₂} (ha : a.comp ρ₁ = ρ)
    (hb : b.comp ρ₂ = ρ) {I : Ideal T} {z : T₁₂} (hz : z ∈ I.map ρ) :
    ∃ z₁ ∈ I.map ρ₁, ∃ z₂ ∈ I.map ρ₂, z = a z₁ + b z₂ := by
  obtain ⟨N, x, hx, hzx⟩ := h.mem_map hz
  obtain ⟨u, w, huw⟩ := hfg.pow (m := N) (n := N)
  obtain ⟨e₁, he₁⟩ := h₁.unit.exists_left_inv
  obtain ⟨e₂, he₂⟩ := h₂.unit.exists_left_inv
  refine ⟨ρ₁ (w * x) * e₁ ^ N, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hx)),
    ρ₂ (u * x) * e₂ ^ N, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hx)), ?_⟩
  have ha' : ∀ t, a (ρ₁ t) = ρ t := fun t => by rw [← ha]; rfl
  have hb' : ∀ t, b (ρ₂ t) = ρ t := fun t => by rw [← hb]; rfl
  have P1 : a e₁ ^ N * ρ f ^ N = 1 := by rw [← mul_pow, ← ha', ← map_mul, he₁, map_one, one_pow]
  have P2 : b e₂ ^ N * ρ g ^ N = 1 := by rw [← mul_pow, ← hb', ← map_mul, he₂, map_one, one_pow]
  have key := congrArg ρ huw
  simp only [map_add, map_mul, map_pow, map_one] at key
  rw [map_mul] at hzx
  simp only [map_mul, map_pow, ha', hb']
  rw [← hzx]
  linear_combination (-z) * key - (ρ w * z * ρ g ^ N) * P1 - (ρ u * z * ρ f ^ N) * P2
end GlobalTheory.SqZero
