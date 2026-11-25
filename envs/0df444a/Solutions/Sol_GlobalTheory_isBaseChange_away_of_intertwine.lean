-- Prove2me | solution 1 for GlobalTheory.isBaseChange_away_of_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:32.147385+00:00
-- url     : https://prove2.me/submissions/7a823234-c1c9-41e9-a526-cac5c2ea5429

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
variable {R₀ R A₀ A : Type} [CommRing R₀] [CommRing R] [CommRing A₀] [CommRing A] [Algebra R₀ R]
  [Algebra R₀ A₀] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  {N₀ N : Type} [AddCommGroup N₀] [Module R₀ N₀] [Module A₀ N₀] [IsScalarTower R₀ A₀ N₀]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module R₀ N]
  [IsScalarTower R₀ R N] [IsScalarTower R₀ A N]
namespace GlobalTheory
theorem _root_.solution (ψ : N₀ →ₗ[R₀] N) (hψ : IsBaseChange R ψ) (x₀ : A₀)
    (x : A) (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y)
    (θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N)
    (hθ : ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y)) : IsBaseChange R θ := by
  let F (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] LocalizedModule.Away x₀ N₀ :=
    ((awayFrac N₀ x₀ k).restrictScalars R₀).baseChange R
  let P (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] N₀ :=
    ((LinearMap.lsmul A₀ N₀ (x₀ ^ k)).restrictScalars R₀).baseChange R
  have hFP (k l : ℕ) (t : R ⊗[R₀] N₀) : F (k + l) (P l t) = F k t := by
    induction t with
    | zero => simp
    | tmul r y => exact congrArg (r ⊗ₜ[R₀] ·) (awayFrac_add_pow_smul x₀ k l y)
    | add a b ha hb => simp only [map_add, ha, hb]
  have hP (l : ℕ) (t : R ⊗[R₀] N₀) : hψ.equiv (P l t) = x ^ l • hψ.equiv t := by
    induction t with
    | zero => simp
    | tmul r y => simp [P, IsBaseChange.equiv_tmul, h, smul_comm r]
    | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  have hF (k : ℕ) (t : R ⊗[R₀] N₀) :
      θ.liftBaseChange R (F k t) = awayFrac N x k (hψ.equiv t) := by
    induction t with
    | zero => simp
    | tmul r y => simp [F, IsBaseChange.equiv_tmul, hθ, LinearMap.map_smul_of_tower]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hsurj (z : R ⊗[R₀] LocalizedModule.Away x₀ N₀) : ∃ k t, F k t = z := by
    induction z with
    | zero => exact ⟨0, 0, map_zero _⟩
    | tmul r z =>
      obtain ⟨k, y, rfl⟩ := exists_awayFrac z
      exact ⟨k, r ⊗ₜ y, by simp [F]⟩
    | add a b ha hb =>
      obtain ⟨k, t, rfl⟩ := ha
      obtain ⟨j, u, rfl⟩ := hb
      exact ⟨k + j, P j t + P k u, by rw [map_add, hFP, add_comm k j, hFP]⟩
  suffices hb : Function.Bijective (θ.liftBaseChange R) from
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hb) fun z => by simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨k, t, rfl⟩ := hsurj z
    rw [hF, awayFrac_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    rw [← hP, map_eq_zero_iff _ hψ.equiv.injective] at hl
    rw [← hFP k l, hl, map_zero]
  · intro z
    obtain ⟨k, y, rfl⟩ := exists_awayFrac z
    obtain ⟨t, rfl⟩ := hψ.equiv.surjective y
    exact ⟨F k t, hF k t⟩
end GlobalTheory
