-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Formal.IsoThick.bijective_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:35:15.213949+00:00
-- url     : https://prove2.me/submissions/f9f502d8-2e9f-4f28-964b-a2fba837136b

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick
namespace GlobalTheory.CompanionTheory.Formal.IsoThick
theorem _root_.solution {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ρA : A →+* A') (ρB : B →+* B') (ψ : A' →+* B')
    (hc : ∀ a, ψ (ρA a) = ρB (φ a)) (s : A)
    (hA : @IsLocalization.Away _ _ s A' _ ρA.toAlgebra)
    (hB : @IsLocalization.Away _ _ (φ s) B' _ ρB.toAlgebra)
    (hker : ∀ k, φ k = 0 → s * k = 0) (hcok : ∀ b, ∃ a, φ s * b = φ a) :
    Function.Bijective ψ := by
  letI := ρA.toAlgebra
  letI := ρB.toAlgebra
  have eA : ∀ a, algebraMap A A' a = ρA a := fun _ => rfl
  have eB : ∀ a, algebraMap B B' a = ρB a := fun _ => rfl
  have uA : IsUnit (ρA s) := IsLocalization.Away.algebraMap_isUnit (S := A') s
  have uB : IsUnit (ρB (φ s)) := IsLocalization.Away.algebraMap_isUnit (S := B') (φ s)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (S := A') s x
    rw [eA, eA] at h
    have h1 : ρB (φ a) = 0 := by
      rw [← hc, ← h, map_mul, hx, zero_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ s)) B' (φ a)).1 h1
    have h2 : φ (s ^ m * a) = 0 := by rw [map_mul, map_pow]; exact hm
    have h3 := hker _ h2
    have h4 : ρA s * (ρA s ^ m * ρA a) = 0 := by
      have := congrArg ρA h3
      simpa [map_mul, map_pow] using this
    have h5 : ρA a = 0 := by
      have := (uA.mul_right_eq_zero).1 h4
      exact ((uA.pow m).mul_right_eq_zero).1 this
    rw [h5] at h
    exact ((uA.pow n).mul_left_eq_zero).1 h
  · intro y
    obtain ⟨n, b, h⟩ := IsLocalization.Away.surj (S := B') (φ s) y
    rw [eB, eB] at h
    obtain ⟨a, ha⟩ := hcok b
    obtain ⟨x, hx⟩ : ∃ x, x * ρA s ^ (n + 1) = ρA a := by
      refine ⟨ρA a * ↑((uA.pow (n + 1)).unit⁻¹), ?_⟩
      rw [mul_assoc]
      have : (↑((uA.pow (n + 1)).unit⁻¹) : A') * ρA s ^ (n + 1) = 1 :=
        (uA.pow (n + 1)).val_inv_mul
      rw [this, mul_one]
    refine ⟨x, ?_⟩
    have h1 : ψ x * ρB (φ s) ^ (n + 1) = y * ρB (φ s) ^ (n + 1) := by
      have := congrArg ψ hx
      rw [map_mul, map_pow, hc, hc, ← ha, map_mul, ← h] at this
      rw [this]; ring
    exact (uB.pow (n + 1)).mul_right_cancel h1
end GlobalTheory.CompanionTheory.Formal.IsoThick
