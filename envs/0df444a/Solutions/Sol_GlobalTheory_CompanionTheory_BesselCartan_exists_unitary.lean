-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.exists_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:38:52.625058+00:00
-- url     : https://prove2.me/submissions/8a73f396-0d27-48a6-8a29-9d6e66b1c191

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_exists_refl
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_dot_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCartan
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) (x y : Fin n → ℂ)
    (h1 : star x ⬝ᵥ x = star y ⬝ᵥ y) (h2 : star x ⬝ᵥ H *ᵥ x = star y ⬝ᵥ H *ᵥ y) :
    ∃ K : Matrix (Fin n) (Fin n) ℂ, Kᴴ * K = 1 ∧ H * K = K * H ∧ K *ᵥ x = y ∧
      ∀ w, star x ⬝ᵥ w = 0 → star y ⬝ᵥ w = 0 → star x ⬝ᵥ H *ᵥ w = 0 → star y ⬝ᵥ H *ᵥ w = 0 → K *ᵥ w = w := by
  classical
  have hHz : ∀ z : Fin n → ℂ, H *ᵥ (H *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec]
  have hpl : ∀ z : Fin n → ℂ, H *ᵥ ((1 / 2 : ℂ) • (z + H *ᵥ z)) = (1 : ℂ) • ((1 / 2 : ℂ) • (z + H *ᵥ z)) := by
    intro z
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hHz, one_smul, add_comm]
  have hmi : ∀ z : Fin n → ℂ, H *ᵥ ((1 / 2 : ℂ) • (z - H *ᵥ z)) = (-1 : ℂ) • ((1 / 2 : ℂ) • (z - H *ᵥ z)) := by
    intro z
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hHz]
    module
  have hst : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hnp : ∀ z : Fin n → ℂ, star ((1 / 2 : ℂ) • (z + H *ᵥ z)) ⬝ᵥ ((1 / 2 : ℂ) • (z + H *ᵥ z)) =
      (1 / 2 : ℂ) * (star z ⬝ᵥ z + star z ⬝ᵥ H *ᵥ z) := by
    intro z
    have e1 := dot_herm H hH z z
    have e2 := dot_herm H hH z (H *ᵥ z)
    rw [hHz] at e2
    simp only [star_smul, star_add, smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul,
      e1, e2, hst]
    ring
  have hnm : ∀ z : Fin n → ℂ, star ((1 / 2 : ℂ) • (z - H *ᵥ z)) ⬝ᵥ ((1 / 2 : ℂ) • (z - H *ᵥ z)) =
      (1 / 2 : ℂ) * (star z ⬝ᵥ z - star z ⬝ᵥ H *ᵥ z) := by
    intro z
    have e1 := dot_herm H hH z z
    have e2 := dot_herm H hH z (H *ᵥ z)
    rw [hHz] at e2
    simp only [star_smul, star_sub, smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, smul_eq_mul,
      e1, e2, hst]
    ring
  have horth1 : ∀ p m : Fin n → ℂ, H *ᵥ p = (1 : ℂ) • p → H *ᵥ m = (-1 : ℂ) • m → star p ⬝ᵥ m = 0 := by
    intro p m hp hm
    have h := dot_herm H hH p m
    rw [hp, hm, one_smul, dotProduct_smul, smul_eq_mul] at h
    linear_combination h / 2
  have horth2 : ∀ p m : Fin n → ℂ, H *ᵥ p = (1 : ℂ) • p → H *ᵥ m = (-1 : ℂ) • m → star m ⬝ᵥ p = 0 := by
    intro p m hp hm
    have h := dot_herm H hH m p
    have hs1 : star (-1 : ℂ) = -1 := by simp
    rw [hp, hm, one_smul, star_smul, smul_dotProduct, smul_eq_mul, hs1] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hpw : ∀ z w : Fin n → ℂ, star z ⬝ᵥ w = 0 → star z ⬝ᵥ H *ᵥ w = 0 →
      star ((1 / 2 : ℂ) • (z + H *ᵥ z)) ⬝ᵥ w = 0 := by
    intro z w hz1 hz2
    rw [star_smul, star_add, smul_dotProduct, add_dotProduct, dot_herm H hH, hz1, hz2, add_zero, smul_zero]
  have hmw : ∀ z w : Fin n → ℂ, star z ⬝ᵥ w = 0 → star z ⬝ᵥ H *ᵥ w = 0 →
      star ((1 / 2 : ℂ) • (z - H *ᵥ z)) ⬝ᵥ w = 0 := by
    intro z w hz1 hz2
    rw [star_smul, star_sub, smul_dotProduct, sub_dotProduct, dot_herm H hH, hz1, hz2, sub_zero, smul_zero]
  have hnp' : star ((1 / 2 : ℂ) • (x + H *ᵥ x)) ⬝ᵥ ((1 / 2 : ℂ) • (x + H *ᵥ x)) =
      star ((1 / 2 : ℂ) • (y + H *ᵥ y)) ⬝ᵥ ((1 / 2 : ℂ) • (y + H *ᵥ y)) := by
    rw [hnp, hnp, h1, h2]
  have hnm' : star ((1 / 2 : ℂ) • (x - H *ᵥ x)) ⬝ᵥ ((1 / 2 : ℂ) • (x - H *ᵥ x)) =
      star ((1 / 2 : ℂ) • (y - H *ᵥ y)) ⬝ᵥ ((1 / 2 : ℂ) • (y - H *ᵥ y)) := by
    rw [hnm, hnm, h1, h2]
  obtain ⟨U₁, hU₁u, hU₁H, hU₁a, hU₁f⟩ := exists_refl H hH 1 (by simp) _ _ (hpl x) (hpl y) hnp'
  obtain ⟨U₂, hU₂u, hU₂H, hU₂a, hU₂f⟩ := exists_refl H hH (-1) (by simp) _ _ (hmi x) (hmi y) hnm'
  have hfix1 : U₁ *ᵥ ((1 / 2 : ℂ) • (x - H *ᵥ x)) = (1 / 2 : ℂ) • (x - H *ᵥ x) :=
    hU₁f _ (horth1 _ _ (hpl x) (hmi x)) (horth1 _ _ (hpl y) (hmi x))
  have hfix2 : U₂ *ᵥ ((1 / 2 : ℂ) • (y + H *ᵥ y)) = (1 / 2 : ℂ) • (y + H *ᵥ y) :=
    hU₂f _ (horth2 _ _ (hpl y) (hmi x)) (horth2 _ _ (hpl y) (hmi y))
  have hx : x = (1 / 2 : ℂ) • (x + H *ᵥ x) + (1 / 2 : ℂ) • (x - H *ᵥ x) := by module
  have hy : (1 / 2 : ℂ) • (y + H *ᵥ y) + (1 / 2 : ℂ) • (y - H *ᵥ y) = y := by module
  refine ⟨U₂ * U₁, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₂ᴴ, hU₂u, Matrix.one_mul, hU₁u]
  · rw [← Matrix.mul_assoc, hU₂H, Matrix.mul_assoc, hU₁H, ← Matrix.mul_assoc]
  · conv_lhs => rw [hx]
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_add, hU₁a, hfix1, Matrix.mulVec_add, hfix2, hU₂a, hy]
  · intro w hw1 hw2 hw3 hw4
    rw [← Matrix.mulVec_mulVec, hU₁f w (hpw x w hw1 hw3) (hpw y w hw2 hw4),
      hU₂f w (hmw x w hw1 hw3) (hmw y w hw2 hw4)]
end GlobalTheory.CompanionTheory.BesselCartan
