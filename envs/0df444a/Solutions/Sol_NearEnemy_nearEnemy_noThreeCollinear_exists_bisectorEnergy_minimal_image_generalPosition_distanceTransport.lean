-- Prove2me | solution 1 for NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:13:22.588827+00:00
-- url     : https://prove2.me/submissions/e01836b1-c7ee-42b4-868e-316981c95812

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_card_dist_image_eq_card_diffClasses
import Theorems.Thm_NearEnemy_dist_image_eq_iff_of_sep
import Theorems.Thm_NearEnemy_injOn_of_projectionGeneric
import Theorems.Thm_NearEnemy_nearEnemy_genericProjection_bisectorEnergy_eq_pairCount
import Theorems.Thm_NearEnemy_nearEnemy_noThreeCollinear_exists_projectionGeneric_image_generalPosition_rotationFree
import Theorems.Thm_NearEnemy_two_mul_pairCount_le_bisectorEnergy

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- **Downstairs rotation-channel vanishing**: a projection that separates
the planar distances of all difference-distinct (non-translation,
non-half-turn) pairs of pairs of `G` has an image with zero rotational
energy — every congruent quadruple of the image is translation or half-turn
related. -/
theorem rotationEnergy_image_eq_zero
    {G : Finset (EuclideanSpace ℝ ι)}
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hsep : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
      a - b ≠ c - e → a - b ≠ -(c - e) →
      dist (T a) (T b) ≠ dist (T c) (T e)) :
    rotationEnergy (G.image fun x ↦ T x) = 0 := by
  rw [rotationEnergy, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨⟨q₁, q₂⟩, q₃, q₄⟩ hq
  simp only [Finset.mem_product] at hq
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h2
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h3
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h4
  rintro ⟨-, -, hdist, hne1, hne2⟩
  by_cases hvw : a - b = c - e
  · refine hne1 ?_
    show T a - T b = T c - T e
    rw [← map_sub, ← map_sub, hvw]
  by_cases hvw' : a - b = -(c - e)
  · refine hne2 ?_
    show T a - T b = -(T c - T e)
    rw [← map_sub, ← map_sub, ← map_neg, hvw']
  exact hsep a ha b hb c hc e he hvw hvw' hdist

/-- **Near Enemy Theorem for Bisector Energy, minimality (conditional
form)**: the image of a finite set under a generic projection attains the
absolute minimum bisector energy among all planar point sets of the same
size. -/
theorem nearEnemy_genericProjection_bisectorEnergy_minimal {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)} {G : Finset (EuclideanSpace ℝ ι)}
    (hT : ProjectionGeneric T G)
    (P' : Finset (EuclideanSpace ℝ (Fin 2))) (hcard : P'.card = G.card) :
    bisectorEnergy (G.image fun x ↦ T x) ≤ bisectorEnergy P' := by
  rw [nearEnemy_genericProjection_bisectorEnergy_eq_pairCount hT, ← hcard]
  exact two_mul_pairCount_le_bisectorEnergy P'

end NearEnemy

open NearEnemy in
theorem solution {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
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
          ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card := by
  obtain ⟨T, hT, htriple, hquad, hsep⟩ :=
    nearEnemy_noThreeCollinear_exists_projectionGeneric_image_generalPosition_rotationFree
      hG
  refine ⟨T, injOn_of_projectionGeneric hT,
    nearEnemy_genericProjection_bisectorEnergy_eq_pairCount hT,
    nearEnemy_genericProjection_bisectorEnergy_minimal hT, ?_, ?_,
    rotationEnergy_image_eq_zero hsep,
    fun a ha b hb c hc e he ↦ dist_image_eq_iff_of_sep hsep ha hb hc he,
    card_dist_image_eq_card_diffClasses hsep⟩
  · intro q₁ hq₁ q₂ hq₂ q₃ hq₃ h₁₂ h₁₃ h₂₃
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
    obtain ⟨p₃, hp₃, rfl⟩ := Finset.mem_image.mp hq₃
    exact htriple p₁ hp₁ p₂ hp₂ p₃ hp₃
      (fun h => h₁₂ (congrArg _ h)) (fun h => h₁₃ (congrArg _ h))
      (fun h => h₂₃ (congrArg _ h))
  · intro q₁ hq₁ q₂ hq₂ q₃ hq₃ q₄ hq₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp hq₂
    obtain ⟨p₃, hp₃, rfl⟩ := Finset.mem_image.mp hq₃
    obtain ⟨p₄, hp₄, rfl⟩ := Finset.mem_image.mp hq₄
    exact hquad p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
      (fun h => h₁₂ (congrArg _ h)) (fun h => h₁₃ (congrArg _ h))
      (fun h => h₁₄ (congrArg _ h)) (fun h => h₂₃ (congrArg _ h))
      (fun h => h₂₄ (congrArg _ h)) (fun h => h₃₄ (congrArg _ h))
