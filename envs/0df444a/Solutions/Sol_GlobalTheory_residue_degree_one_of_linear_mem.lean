-- Prove2me | solution 1 for GlobalTheory.residue_degree_one_of_linear_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:46.641382+00:00
-- url     : https://prove2.me/submissions/62a7a768-d3d6-464b-bd10-01a5597290ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ResidueDegreeOneOfLinearMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  intro A B _ _ _ P _ θ D a b hmax hgen hD hb hab y
  obtain ⟨b', i, hi, hbi⟩ := hmax.exists_inv (x := b) (by rwa [Ideal.mem_comap])
  obtain ⟨D', j, hj, hDj⟩ := hmax.exists_inv (x := D) (by rwa [Ideal.mem_comap])
  rw [Ideal.mem_comap] at hi hj
  obtain ⟨u, v, hy⟩ := hgen y
  have hbi' := congrArg (algebraMap A B) hbi
  have hDj' := congrArg (algebraMap A B) hDj
  simp only [map_add, map_mul, map_one] at hbi' hDj'
  refine ⟨D' * (u - v * a * b'), ?_⟩
  have key : y - algebraMap A B (D' * (u - v * a * b')) =
      algebraMap A B D' * algebraMap A B v * algebraMap A B b' * (algebraMap A B a + algebraMap A B b * θ)
      + (algebraMap A B D' * algebraMap A B v * θ) * algebraMap A B i + y * algebraMap A B j := by
    simp only [map_sub, map_mul]
    linear_combination algebraMap A B D' * hy - y * hDj' - algebraMap A B D' * algebraMap A B v * θ * hbi'
  rw [key]
  exact P.add_mem (P.add_mem (P.mul_mem_left _ hab) (P.mul_mem_left _ hi)) (P.mul_mem_left _ hj)
end GlobalTheory
