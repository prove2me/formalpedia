-- Prove2me | solution 1 for NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:15:05.337442+00:00
-- url     : https://prove2.me/submissions/fa1540a6-acc9-4ba6-aa2b-778b08070c1a

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- Three distinct points of one Euclidean sphere are never collinear: a
line meets a sphere in at most two points.  This is the bridge showing the
general-position form of the theorem subsumes the sphere-slice form. -/
theorem not_collinear_of_mem_sphere
    {ι : Type*} [Fintype ι]
    {center p₁ p₂ p₃ : EuclideanSpace ℝ ι} {R : ℝ}
    (h₁ : p₁ ∈ Metric.sphere center R)
    (h₂ : p₂ ∈ Metric.sphere center R)
    (h₃ : p₃ ∈ Metric.sphere center R)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι)) := by
  have hcos : EuclideanGeometry.Cospherical
      ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι)) := by
    refine ⟨center, R, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact Metric.mem_sphere.mp h₁
    · exact Metric.mem_sphere.mp h₂
    · exact Metric.mem_sphere.mp h₃
  exact affineIndependent_iff_not_collinear_set.mp
    (hcos.affineIndependent_of_ne h₁₂ h₁₃ h₂₃)

end NearEnemy

open NearEnemy in
theorem solution {center : EuclideanSpace ℝ ι} {R : ℝ} {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ x ∈ G, x ∈ Metric.sphere center R) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) ∧
      (∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P') ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
          ¬ Collinear ℝ ({q₁, q₂, q₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), ∀ q₄ ∈ G.image (fun x ↦ T x),
        q₁ ≠ q₂ → q₁ ≠ q₃ → q₁ ≠ q₄ → q₂ ≠ q₃ → q₂ ≠ q₄ → q₃ ≠ q₄ →
          ¬ EuclideanGeometry.Cospherical
            ({q₁, q₂, q₃, q₄} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      rotationEnergy (G.image fun x ↦ T x) = 0 ∧
      (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
        (dist (T a) (T b) = dist (T c) (T e) ↔
          (a - b = c - e ∨ a - b = -(c - e)))) ∧
      (((G.image fun x ↦ T x).offDiag).image fun q ↦ dist q.1 q.2).card =
        ((G.offDiag).image fun p ↦
          ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card :=
  nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
    fun _p₁ h₁ _p₂ h₂ _p₃ h₃ h₁₂ h₁₃ h₂₃ =>
      not_collinear_of_mem_sphere (hG _ h₁) (hG _ h₂) (hG _ h₃) h₁₂ h₁₃ h₂₃
