-- Prove2me | solution 1 for OAI.Kadison.CompactAverage.exists_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:10:53.694284+00:00
-- url     : https://prove2.me/submissions/f38f938d-db1b-44ec-9e7c-5a401c30ee33

import Mathlib
import Definitions.Def_OAIQ039C004

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContinuity

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : X → E →ₗᵢ[ℂ] E)

lemma joint (h : ∀ x, Continuous fun g => T g x) : Continuous (fun p : X × E => T p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro g
    exact (T g).isometry.lipschitz
  · exact h

end Kadison.StrongContinuity

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakOperatorIntegral
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory Filter

namespace Kadison.WeakOperatorIntegral

variable {ι E F : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem exists_integral (μ : Measure ι) [IsProbabilityMeasure μ]
    (T : ι → E →L[ℂ] F) (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    ∃ V : E →L[ℂ] F, ‖V‖ ≤ C ∧ ∀ x y,
      inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ := by
  let L : E → F → ℂ := fun x y => ∫ i, inner ℂ (T i x) y ∂μ
  have hL : ∀ x y, ‖L x y‖ ≤ C*‖x‖*‖y‖ := by
    intro x y
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun i => inner ℂ (T i x) y)
      (C := C*‖x‖*‖y‖) (Eventually.of_forall (fun i =>
        (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg y))))
    simpa only [probReal_univ,mul_one] using h
  have haddY : ∀ x y z, L x (y+z)=L x y+L x z := by
    intro x y z
    simp only [L,inner_add_right,integral_add (hI x y) (hI x z)]
  have hsmulY : ∀ x (a : ℂ) y, L x (a • y)=a * L x y := by
    intro x a y
    simp only [L,inner_smul_right,integral_const_mul]
  let q : E → StrongDual ℂ F := fun x =>
    ({ toFun := L x
       map_add' := haddY x
       map_smul' := fun a y => hsmulY x a y } : F →ₗ[ℂ] ℂ).mkContinuous
      (C*‖x‖) (hL x)
  have hq : ∀ x y, q x y=L x y := fun _ _ => rfl
  have haddX : ∀ x z y, L (x+z) y=L x y+L z y := by
    intro x z y
    simp only [L,map_add,inner_add_left,integral_add (hI x y) (hI z y)]
  have hsmulX : ∀ (a : ℂ) x y, L (a • x) y=star a * L x y := by
    intro a x y
    simp only [L,map_smul,inner_smul_left,RCLike.star_def,integral_const_mul]
  let V₀ : E →ₗ[ℂ] F :=
    { toFun := fun x => (InnerProductSpace.toDual ℂ F).symm (q x)
      map_add' := by
        intro x z
        apply ext_inner_right ℂ
        intro y
        simp only [inner_add_left,InnerProductSpace.toDual_symm_apply,hq,haddX]
      map_smul' := by
        intro a x
        apply ext_inner_right ℂ
        intro y
        simp only [inner_smul_left,InnerProductSpace.toDual_symm_apply,hq,hsmulX,
          RingHom.id_apply,RCLike.star_def] }
  have hV : ∀ x, ‖V₀ x‖ ≤ C*‖x‖ := by
    intro x
    change ‖(InnerProductSpace.toDual ℂ F).symm (q x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hC (norm_nonneg x)) (hL x)
  refine ⟨V₀.mkContinuous C hV,LinearMap.mkContinuous_norm_le _ hC hV,?_⟩
  intro x y
  exact InnerProductSpace.toDual_symm_apply

end Kadison.WeakOperatorIntegral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CompactAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure

namespace Kadison.CompactAverage

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ x : H, Continuous fun g => U g x)

variable (Y : H →L[ℂ] H)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
include hU in
lemma conjugate_continuous (x : H) : Continuous fun g => conjugate U Y g x := by
  have hi : Continuous fun g => (U g).symm x := by
    simpa only [Function.comp_def, map_inv,LinearIsometryEquiv.coe_inv] using (hU x).comp continuous_inv
  have hj := StrongContinuity.joint (fun g => (U g).toLinearIsometry) hU
  exact hj.comp (continuous_id.prodMk (Y.continuous.comp hi))

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
lemma conjugate_norm (g : G) : ‖conjugate U Y g‖ = ‖Y‖ := by
  exact StarAlgEquiv.norm_map (U g).conjStarAlgEquiv Y

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
lemma conjugate_covariant (g k : G) :
    (U g : H →L[ℂ] H) * conjugate U Y k = conjugate U Y (g*k) * (U g : H →L[ℂ] H) := by
  ext x
  simp [conjugate,mul_apply_eq_comp,map_mul,LinearIsometryEquiv.mul_def]

include hU in
theorem exists_average_oai (μ : Measure G) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ] :
    ∃ V : H →L[ℂ] H, ‖V‖ ≤ ‖Y‖ ∧
      (∀ g, V * (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) * V) ∧
      (∀ x y, inner ℂ (V x) y = ∫ g, inner ℂ (conjugate U Y g x) y ∂μ) := by
  have hI : ∀ x y, Integrable (fun g => inner ℂ (conjugate U Y g x) y) μ := by
    intro x y
    exact ((conjugate_continuous U hU Y x).inner continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨V,hb,hV⟩ := WeakOperatorIntegral.exists_integral μ (conjugate U Y) hI ‖Y‖
    (norm_nonneg _) (fun g => (conjugate_norm U Y g).le)
  refine ⟨V,hb,?_,hV⟩
  intro g
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_right (U g : H →L[ℂ] H),hV,hV]
  have hc : ∀ k, inner ℂ (conjugate U Y k x) ((U g : H →L[ℂ] H).adjoint y) =
      inner ℂ (conjugate U Y (g*k) ((U g) x)) y := by
    intro k
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact congrArg (fun A : H →L[ℂ] H => inner ℂ (A x) y) (conjugate_covariant U Y g k)
  simp_rw [hc]
  exact (integral_mul_left_eq_self (fun k => inner ℂ (conjugate U Y k ((U g) x)) y) g).symm

end Kadison.CompactAverage

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.CompactAverage.exists_average_oai.{u_1, u_2} := @OAI.Kadison.CompactAverage.exists_average_oai.{u_1, u_2}
