-- Prove2me | solution 1 for OAI.HochschildNormalPart.normalProjection_fixes_normal
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:48:27.396711+00:00
-- url     : https://prove2.me/submissions/3fd2d661-dd3e-4589-a1b3-ad2142165e3d

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

lemma coefficient_norm (η ξ : H) : ‖coefficient π η ξ‖ ≤ ‖η‖*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := by gcongr; exact (π a).le_opNorm ξ
    _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

omit [CompleteSpace X] in
lemma normalVectors_commutant {ξ : H} (hξ : ξ ∈ normalVectors e π)
    (T : H →L[ℂ] H) (hT : ∀ a : M, T * π a=π a*T) :
    T ξ ∈ normalVectors e π := by
  rw [mem_normalVectors] at hξ ⊢
  intro η
  have hc : coefficient π η (T ξ)=coefficient π (star T η) ξ := by
    ext a
    change ⟪η,π a (T ξ)⟫_ℂ=⟪T.adjoint η,π a ξ⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (inner ℂ η) (congrArg (fun S : H →L[ℂ] H => S ξ) (hT a).symm)
  rw [hc]
  exact hξ _

lemma projection_commutes (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : ∀ ξ ∈ K, T ξ ∈ K) (hTstar : ∀ ξ ∈ K, star T ξ ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext ξ
  change K.starProjection (T ξ)=T (K.starProjection ξ)
  apply Submodule.eq_starProjection_of_mem_orthogonal (hT _ (by simp))
  intro η hη
  change ⟪η,T ξ-T (K.starProjection ξ)⟫_ℂ=0
  rw [← map_sub]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact K.sub_starProjection_mem_orthogonal ξ _ (hTstar η hη)

lemma normalProjection_commutant (T : H →L[ℂ] H)
    (hT : ∀ a : M, T*π a=π a*T) :
    normalProjection e π*T=T*normalProjection e π := by
  apply projection_commutes
  · intro ξ hξ; exact normalVectors_commutant e π hξ T hT
  · intro ξ hξ
    apply normalVectors_commutant e π hξ
    intro a
    have h := congrArg star (hT (star a))
    simpa only [star_mul,← map_star,star_star] using h.symm

def coefficientLeft (ξ : H) : H →L⋆[ℂ] StrongDual ℂ M := by
  let L : H →ₗ⋆[ℂ] StrongDual ℂ M :=
    { toFun := fun η => coefficient π η ξ
      map_add' := by intro η ζ; ext a; simp
      map_smul' := by intro r η; ext a; simp [mul_comm] }
  exact L.mkContinuous ‖ξ‖ (fun η => by
    change ‖coefficient π η ξ‖ ≤ ‖ξ‖*‖η‖
    simpa only [mul_comm] using coefficient_norm π η ξ)

@[simp] lemma coefficientLeft_apply (ξ η : H) :
    coefficientLeft π ξ η=coefficient π η ξ := rfl

def cyclicSpace (ξ : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure

lemma cyclicSpace_closed (ξ : H) : IsClosed (cyclicSpace π ξ : Set H) :=
  Submodule.isClosed_topologicalClosure _

instance cyclicSpace_complete (ξ : H) : CompleteSpace (cyclicSpace π ξ) :=
  (cyclicSpace_closed π ξ).completeSpace_coe

lemma cyclicSpace_mem (ξ : H) : ξ ∈ cyclicSpace π ξ := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

lemma cyclicSpace_mul (ξ : H) (b : M) {ζ : H} (hζ : ζ ∈ cyclicSpace π ξ) :
    π b ζ ∈ cyclicSpace π ξ := by
  let S := cyclicSpace π ξ
  have hle : (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure ≤
      S.comap (π b).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      change π b (π a ξ) ∈ S
      change π b (π a ξ) ∈ (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure
      apply Submodule.le_topologicalClosure
      rw [← mul_apply_eq_comp,← map_mul]
      exact Submodule.subset_span (Set.mem_range_self (b*a))
    · exact (cyclicSpace_closed π ξ).preimage (π b).continuous
  exact hle hζ

lemma cyclicProjection_mul (ξ : H) (a : M) :
    (cyclicSpace π ξ).starProjection*π a=π a*(cyclicSpace π ξ).starProjection := by
  apply projection_commutes
  · intro ζ hζ; exact cyclicSpace_mul π ξ a hζ
  · intro ζ hζ
    rw [← map_star]
    exact cyclicSpace_mul π ξ (star a) hζ

lemma cyclic_coefficients_normal (η ξ : H)
    (h : coefficient π η ξ ∈ normalDual e) {ζ : H} (hζ : ζ ∈ cyclicSpace π η) :
    coefficient π ζ ξ ∈ normalDual e := by
  let S := (normalDual e).comap (coefficientLeft π ξ).toLinearMap
  have hle : cyclicSpace π η ≤ S := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨b,rfl⟩
      change coefficient π (π b η) ξ ∈ normalDual e
      have hc : coefficient π (π b η) ξ=(coefficient π η ξ).comp
          (ContinuousLinearMap.mul ℂ M (star b)) := by
        ext a
        change ⟪π b η,π a ξ⟫_ℂ=⟪η,π (star b*a) ξ⟫_ℂ
        rw [map_mul,mul_apply_eq_comp,map_star]
        exact (ContinuousLinearMap.adjoint_inner_right (π b) η (π a ξ)).symm
      rw [hc]
      exact normalDual_comp e h _ ((HochschildSakai.abstract_multiplication_normal e).1 _)
    · exact (normalDual_closed e).preimage (coefficientLeft π ξ).continuous
  exact hle hζ

lemma normalProjection_fixes_normal (η ξ : H)
    (h : coefficient π η ξ ∈ normalDual e) :
    coefficient π η (normalProjection e π ξ)=coefficient π η ξ := by
  let K := cyclicSpace π η
  let Q := K.starProjection
  have hQ : ∀ a : M, Q*π a=π a*Q := cyclicProjection_mul π η
  have hcoef (ζ : H) : coefficient π ζ (Q ξ)=coefficient π (Q ζ) ξ := by
    ext a
    change ⟪ζ,π a (Q ξ)⟫_ℂ=⟪Q ζ,π a ξ⟫_ℂ
    have hc := congrArg (fun T : H →L[ℂ] H => T ξ) (hQ a)
    change Q (π a ξ)=π a (Q ξ) at hc
    rw [← hc]
    exact (K.inner_starProjection_left_eq_right ζ (π a ξ)).symm
  have hn : Q ξ ∈ normalVectors e π := by
    rw [mem_normalVectors]
    intro ζ
    rw [hcoef]
    exact cyclic_coefficients_normal e π η ξ h (by simp [Q,K])
  have hP : normalProjection e π (Q ξ)=Q ξ :=
    Submodule.starProjection_eq_self_iff.mpr hn
  have hcomm := congrArg (fun T : H →L[ℂ] H => T ξ) (normalProjection_commutant e π Q hQ)
  change normalProjection e π (Q ξ)=Q (normalProjection e π ξ) at hcomm
  have hη : Q η=η := Submodule.starProjection_eq_self_iff.mpr (cyclicSpace_mem π η)
  calc
    coefficient π η (normalProjection e π ξ) = coefficient π (Q η) (normalProjection e π ξ) := by rw [hη]
    _ = coefficient π η (Q (normalProjection e π ξ)) := by
      ext a
      change ⟪Q η,π a (normalProjection e π ξ)⟫_ℂ=⟪η,π a (Q (normalProjection e π ξ))⟫_ℂ
      rw [K.inner_starProjection_left_eq_right]
      exact congrArg (inner ℂ η) (congrArg (fun T : H →L[ℂ] H => T (normalProjection e π ξ)) (hQ a))
    _ = coefficient π η (Q ξ) := by rw [← hcomm,hP]
    _ = coefficient π (Q η) ξ := hcoef η
    _ = coefficient π η ξ := by rw [hη]
end HochschildNormalPart
end
end OAI
end

theorem solution.{u,v} : type_of% @OAI.HochschildNormalPart.normalProjection_fixes_normal.{u,v} := @OAI.HochschildNormalPart.normalProjection_fixes_normal.{u,v}
