-- Prove2me | solution 1 for OAI.HochschildNormalPart.normalProjection_sum
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:53:10.592553+00:00
-- url     : https://prove2.me/submissions/927552d0-61bf-439e-a437-5c652dc49b49

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [CompleteSpace X]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

end HochschildNormalPart

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma coefficient_sum (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (η ξ : WithLp 2 (H×K)) :
    coefficient (sumRepresentation π ρ) η ξ=
      coefficient π η.fst ξ.fst+coefficient ρ η.snd ξ.snd := by
  ext a; rfl

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [CompleteSpace X] in
lemma mem_normalVectors_sum (ξ : WithLp 2 (H×K)) :
    ξ ∈ normalVectors e (sumRepresentation π ρ) ↔
      ξ.fst ∈ normalVectors e π ∧ ξ.snd ∈ normalVectors e ρ := by
  simp only [mem_normalVectors,coefficient_sum]
  constructor
  · intro h
    constructor
    · intro η
      have h' := h (WithLp.toLp 2 (η,0))
      change coefficient π η ξ.fst+coefficient ρ 0 ξ.snd ∈ normalDual e at h'
      have hz : coefficient ρ 0 ξ.snd=0 := by ext a; simp
      simpa only [hz,add_zero] using h'
    · intro η
      have h' := h (WithLp.toLp 2 (0,η))
      change coefficient π 0 ξ.fst+coefficient ρ η ξ.snd ∈ normalDual e at h'
      have hz : coefficient π 0 ξ.fst=0 := by ext a; simp
      simpa only [hz,zero_add] using h'
  · rintro ⟨hπ,hρ⟩ η
    exact (normalDual e).add_mem (hπ η.fst) (hρ η.snd)

lemma normalProjection_sum (ξ : WithLp 2 (H×K)) :
    normalProjection e (sumRepresentation π ρ) ξ=
      WithLp.toLp 2 (normalProjection e π ξ.fst,normalProjection e ρ ξ.snd) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [mem_normalVectors_sum]
    change normalProjection e π ξ.fst ∈ normalVectors e π ∧
      normalProjection e ρ ξ.snd ∈ normalVectors e ρ
    exact ⟨by simp [normalProjection],by simp [normalProjection]⟩
  · intro η hη
    obtain ⟨hη₁,hη₂⟩ := (mem_normalVectors_sum e π ρ η).mp hη
    change ⟪η,ξ-WithLp.toLp 2 (normalProjection e π ξ.fst,normalProjection e ρ ξ.snd)⟫_ℂ=0
    change ⟪η.fst,ξ.fst-normalProjection e π ξ.fst⟫_ℂ+
      ⟪η.snd,ξ.snd-normalProjection e ρ ξ.snd⟫_ℂ=0
    unfold normalProjection
    rw [(normalVectors e π).sub_starProjection_mem_orthogonal ξ.fst η.fst hη₁,
      (normalVectors e ρ).sub_starProjection_mem_orthogonal ξ.snd η.snd hη₂,add_zero]
end HochschildNormalPart
end
end OAI
end

theorem solution.{u,v,w} : type_of% @OAI.HochschildNormalPart.normalProjection_sum.{u,v,w} := @OAI.HochschildNormalPart.normalProjection_sum.{u,v,w}
