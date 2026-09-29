-- Prove2me | solution 1 for NearEnemy.nearEnemy_genericProjection_bisectorEnergy_eq_pairCount
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:00:07.530399+00:00
-- url     : https://prove2.me/submissions/1a94d87a-9b4f-420f-ad6b-a0273471daf4

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_bisectorEnergy_eq_of_bisectorInjective
import Theorems.Thm_NearEnemy_injOn_of_projectionGeneric
import Theorems.Thm_NearEnemy_sharedBisector_parallel_and_sum_orth

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- **Shared-bisector criterion under a generic projection**: if a projection
is generic for `G` and two nondegenerate pairs from `G` acquire the same
perpendicular bisector downstairs, they were the same unordered pair
upstairs.  Sphere-free: coincidence-avoidance forbids every off-pair
quadruple directly; the sphere enters only the existence statement for a
generic `T`. -/
theorem nearEnemy_sharedBisector_forces_samePair
    {ι : Type*} [Fintype ι]
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    {G : Finset (EuclideanSpace ℝ ι)}
    (hT : ProjectionGeneric T G)
    {a b c e : EuclideanSpace ℝ ι}
    (ha : a ∈ G) (hb : b ∈ G) (hc : c ∈ G) (he : e ∈ G)
    (hab : a ≠ b) (hce : c ≠ e)
    (hbis : perpBisector (T a) (T b) = perpBisector (T c) (T e)) :
    ({a, b} : Set (EuclideanSpace ℝ ι)) = {c, e} := by
  by_contra hne
  obtain ⟨-, havoid⟩ := hT
  apply havoid a ha b hb c hc e he hab hce hne
  obtain ⟨⟨t, ht⟩, horth⟩ := sharedBisector_parallel_and_sum_orth hbis
  constructor
  · -- (1) downstairs parallelism transfers through linearity with the same
    -- scalar: `T e - T c = t • (T b - T a)` rewrites to
    -- `T (c - e) = t • T (a - b)`.
    refine ⟨t, ?_⟩
    rw [map_sub, map_sub]
    linear_combination (norm := module) -ht
  · -- (2) downstairs orthogonality transfers through linearity up to sign.
    have e1 : T (a + b - (c + e)) = T a + T b - (T c + T e) := by
      rw [map_sub, map_add, map_add]
    have e2 : T (a - b) = -(T b - T a) := by
      rw [map_sub]
      module
    rw [e1, e2, inner_neg_right, horth, neg_zero]

/-- **Bisector injectivity downstairs**: under a generic projection, the
bisector map is injective on unordered pairs of the projected set. -/
theorem nearEnemy_bisectors_injective_on_unorderedPairs {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)} {G : Finset (EuclideanSpace ℝ ι)}
    (hT : ProjectionGeneric T G) :
    BisectorInjectiveOnPairs (G.image fun x ↦ T x) := by
  intro p hp q hq p' hp' q' hq' hpq hpq' hbis
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq'
  have hab : a ≠ b := fun h ↦ hpq (by rw [h])
  have hce : c ≠ e := fun h ↦ hpq' (by rw [h])
  have hpair := nearEnemy_sharedBisector_forces_samePair hT ha hb hc he hab hce hbis
  calc ({T a, T b} : Set (EuclideanSpace ℝ (Fin 2)))
      = (fun x ↦ T x) '' {a, b} := (Set.image_pair _ _ _).symm
    _ = (fun x ↦ T x) '' {c, e} := by rw [hpair]
    _ = {T c, T e} := Set.image_pair _ _ _

end NearEnemy

open NearEnemy in
theorem solution {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)} {G : Finset (EuclideanSpace ℝ ι)} (hT : ProjectionGeneric T G) :
    bisectorEnergy (G.image fun x ↦ T x) = 2 * G.card * (G.card - 1) := by
  rw [bisectorEnergy_eq_of_bisectorInjective
    (nearEnemy_bisectors_injective_on_unorderedPairs hT),
    Finset.card_image_of_injOn (injOn_of_projectionGeneric hT)]
