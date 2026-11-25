-- Prove2me | solution 1 for GlobalTheory.exists_away_map_of_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:21.308128+00:00
-- url     : https://prove2.me/submissions/9fa21383-c12b-407e-aa47-875853beec41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
import Theorems.Thm_GlobalTheory_exists_awayFrac_common
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
omit [Algebra R A] [IsScalarTower R₀ R A] [Module R N] [IsScalarTower R A N]
  [IsScalarTower R₀ R N]
namespace GlobalTheory
theorem _root_.solution (ψ : N₀ →ₗ[R₀] N) (x₀ : A₀) (x : A)
    (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y) :
    ∃ θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N,
      ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y) := by
  choose d n hdn using fun z : LocalizedModule.Away x₀ N₀ => exists_awayFrac z
  have key (k : ℕ) (y : N₀) :
      awayFrac N x (d (awayFrac N₀ x₀ k y)) (ψ (n (awayFrac N₀ x₀ k y))) =
        awayFrac N x k (ψ y) := by
    obtain ⟨l, hl⟩ := awayFrac_eq_iff.1 (hdn (awayFrac N₀ x₀ k y))
    exact awayFrac_eq_iff.2 ⟨l, by rw [← h, ← h, hl]⟩
  refine ⟨⟨⟨fun z => awayFrac N x (d z) (ψ (n z)), fun z w => ?_⟩, fun r z => ?_⟩, key⟩
  · obtain ⟨k, m, m', rfl, rfl⟩ := exists_awayFrac_common z w
    rw [← map_add, key, key, key, map_add, map_add]
  · obtain ⟨k, m, rfl⟩ := exists_awayFrac z
    simp only [RingHom.id_apply]
    rw [← LinearMap.map_smul_of_tower, key, key, map_smul, LinearMap.map_smul_of_tower]
end GlobalTheory
