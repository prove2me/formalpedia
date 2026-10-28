-- Prove2me | solution 1 for OAI.Kadison.uniform_commutator_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:10:37.615695+00:00
-- url     : https://prove2.me/submissions/2ab4151c-5936-4998-b92e-3ad7387f0bdc

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C030
import Theorems.Thm_OAI_Kadison_CompactAverage_exists_average
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_Average
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

omit [CompleteSpace H] in
include hV in
lemma norm_le_of_integral {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    rw [hV]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun i => inner ℂ (T i x) (V x)) (C := C*‖x‖*‖V x‖)
      (Eventually.of_forall (fun i => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg _))))
    simpa only [probReal_univ,mul_one] using h
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm,mul_left_comm,mul_assoc] using hi)

end Kadison.WeakOperatorIntegral

namespace Kadison.WeakOperatorIntegral

open MeasureTheory Filter

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

omit [CompleteSpace H] in
include hI hV in
lemma difference_coeff (W : H →L[ℂ] H) (x y : H) :
    inner ℂ ((V-W) x) y = ∫ i, inner ℂ ((T i-W) x) y ∂μ := by
  simp only [sub_apply,inner_sub_left]
  rw [hV,integral_sub (hI x y) (integrable_const _)]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]

omit [CompleteSpace H] in
include hI hV in
lemma difference_norm (W : H →L[ℂ] H) {C : ℝ} (hC : 0≤C)
    (hb : ∀ i, ‖T i-W‖≤C) : ‖V-W‖≤C :=
  norm_le_of_integral μ (fun i => T i-W) (V-W) (difference_coeff μ T hI V hV W) hC hb

end Kadison.WeakOperatorIntegral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
-- module Solutions.OAIQ039_CM.Commutator_CompactAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

end Kadison.CompactAverage

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteDimensionalAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap MeasureTheory

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma algebraUnitaryRepresentation_continuous (P : VonNeumannAlgebra K) (x : K) :
    Continuous fun v : unitary P => algebraUnitaryRepresentation P v x := by
  change Continuous fun v : unitary P => ((v:P):K →L[ℂ] K) x
  exact (continuous_subtype_val.comp continuous_subtype_val).clm_apply continuous_const

lemma commutes_algebra_of_commutes_unitaries (P : VonNeumannAlgebra K) (T : K →L[ℂ] K)
    (hT : ∀ v : unitary P,T*((v:P):K →L[ℂ] K)=((v:P):K →L[ℂ] K)*T) :
    ∀ a : P,T*(a:K →L[ℂ] K)=(a:K →L[ℂ] K)*T := by
  have hz : innerDerivation P T=0 := by
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.ext_on (CStarAlgebra.span_unitary P)
    intro v hv
    exact sub_eq_zero.mpr (hT ⟨v,hv⟩)
  intro a
  exact sub_eq_zero.mp (congrArg (fun f : P →L[ℂ] (K →L[ℂ] K) => f a) hz)

lemma unitary_conjugate_distance (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (v : unitary P) :
    ‖CompactAverage.conjugate (algebraUnitaryRepresentation P) Y v-Y‖ ≤ commutatorSeminorm P Y := by
  let w : unitary (K →L[ℂ] K) := algebraUnitaryLift P v
  have he : CompactAverage.conjugate (algebraUnitaryRepresentation P) Y v-Y=
      (((w:K →L[ℂ] K)*Y-Y*(w:K →L[ℂ] K))*star (w:K →L[ℂ] K)) := by
    change (w:K →L[ℂ] K)*Y*star (w:K →L[ℂ] K)-Y=_
    rw [sub_mul,mul_assoc Y (w:K →L[ℂ] K) (star (w:K →L[ℂ] K)),w.property.2,mul_one]
  rw [he]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem w.property), norm_sub_rev]
  apply commutator_bound_unitball P Y (v:P).property
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(w:K →L[ℂ] K) x‖≤1*‖x‖
  rw [one_mul]
  exact (Unitary.norm_map w x).le

theorem finiteDimensional_commutant_approximation (P : VonNeumannAlgebra K)
    [FiniteDimensional ℂ P] (Y : K →L[ℂ] K) :
    ∃ Y₀ : K →L[ℂ] K, (∀ a : P,Y₀*(a:K →L[ℂ] K)=(a:K →L[ℂ] K)*Y₀) ∧
      ‖Y-Y₀‖ ≤ commutatorSeminorm P Y := by
  cases subsingleton_or_nontrivial K with
  | inl h =>
    exact ⟨Y,fun a => Subsingleton.elim _ _,by simpa using commutatorSeminorm_nonneg P Y⟩
  | inr h =>
    let := UnitaryHaar.compactUnitary P
    let : MeasurableSpace (unitary P) := borel (unitary P)
    let : BorelSpace (unitary P) := ⟨rfl⟩
    let U := algebraUnitaryRepresentation P
    have hU := algebraUnitaryRepresentation_continuous P
    let μ := UnitaryHaar.probability (unitary P)
    obtain ⟨Y₀,_,hc,hcoeff⟩ := CompactAverage.exists_average U hU Y μ
    refine ⟨Y₀,commutes_algebra_of_commutes_unitaries P Y₀ hc,?_⟩
    rw [norm_sub_rev]
    apply WeakOperatorIntegral.difference_norm μ (CompactAverage.conjugate U Y) _ Y₀ hcoeff Y
      (commutatorSeminorm_nonneg P Y) (unitary_conjugate_distance P Y)
    intro x y
    exact ((CompactAverage.conjugate_continuous U hU Y x).inner continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainCommutantDistance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma diagonal_matrix_commute (h : ℕ) (Z : K →L[ℂ] K)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K))
    (hZ : ∀ i j,Z*X i j=X i j*Z) :
    diagonalAmplification h Z*matrixOperator h X=matrixOperator h X*diagonalAmplification h Z := by
  ext x i
  simp only [mul_apply_eq_comp,diagonalAmplification_apply,matrixOperator_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun A : K →L[ℂ] K => A (x j)) (hZ i j)

omit [CompleteSpace K] in
lemma operator_commutator_norm_le (Y Z : K →L[ℂ] K) : ‖Y*Z-Z*Y‖≤2*‖Y‖*‖Z‖ := by
  calc
    _ ≤ ‖Y*Z‖+‖Z*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖Z‖+‖Z‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

theorem matrix_commutator_bound_of_commutant_approximation
    (P : VonNeumannAlgebra K) (Y Z : K →L[ℂ] K) {c : ℝ} (hc : ‖Y-Z‖ ≤ c)
    (hZ : ∀ a : P,Z*(a:K →L[ℂ] K)=(a:K →L[ℂ] K)*Z)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      2*c*‖matrixOperator h X‖ := by
  have hcomm := diagonal_matrix_commute h Z X (fun i j => hZ ⟨X i j,hX i j⟩)
  have he : diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y=
      diagonalAmplification h (Y-Z)*matrixOperator h X-matrixOperator h X*diagonalAmplification h (Y-Z) := by
    rw [diagonalAmplification_sub,sub_mul,mul_sub,hcomm]
    abel
  rw [he]
  exact (operator_commutator_norm_le _ _).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((diagonalAmplification_norm_le h (Y-Z)).trans hc) (by norm_num))
    (norm_nonneg _))

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteDimensionalMain
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem uniform_commutator_finiteDimensional_oai
    (P : VonNeumannAlgebra K) [FiniteDimensional ℂ P]
    (Y : K →L[ℂ] K) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      2*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨Y₀,hcomm,hnear⟩ := finiteDimensional_commutant_approximation P Y
  exact matrix_commutator_bound_of_commutant_approximation P Y Y₀ hnear hcomm h X hX

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.uniform_commutator_finiteDimensional_oai.{u} := @OAI.Kadison.uniform_commutator_finiteDimensional_oai.{u}
