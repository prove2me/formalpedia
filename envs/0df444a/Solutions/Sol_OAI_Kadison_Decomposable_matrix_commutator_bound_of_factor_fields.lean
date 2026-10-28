-- Prove2me | solution 1 for OAI.Kadison.Decomposable.matrix_commutator_bound_of_factor_fields
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:37:09.367683+00:00
-- url     : https://prove2.me/submissions/034fd73c-c0d9-4272-a2e2-2b62327e023d

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C044
import Theorems.Thm_OAI_Kadison_uniform_commutator_separable_factor

section
-- module Solutions.OAIQ039_CM.Commutator_DiagonalField
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma assemble_diagonal_ae (h : ℕ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (f : PiLp 2 (fun _ : Fin h => Lp H 2 μ)) :
    assemble μ (diagonalAmplification h (operator μ T hm hb) f)=ᵐ[μ]
    fun a => diagonalAmplification h (T a) (assemble μ f a) := by
  have he : ∀ᵐ a ∂μ,∀ i,operator μ T hm hb (f i) a=T a (f i a) :=
    ae_all_iff.mpr (fun i => operator_ae μ _ _ _ (f i))
  filter_upwards [assemble_ae μ (diagonalAmplification h (operator μ T hm hb) f),
    assemble_ae μ f,he] with a ha hf he
  rw [ha,hf]
  ext i
  exact he i

lemma diagonal_conjugate (h : ℕ) (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    (finiteSumEquiv μ).conjStarAlgEquiv (diagonalAmplification h (operator μ T hm hb))=
    operator μ (fun a => diagonalAmplification h (T a))
      (diagonal_field_measurable μ h T hm) (diagonal_field_bound μ h T hb) := by
  apply operator_eq_of_ae_apply
  intro f
  have hh := assemble_diagonal_ae μ h T hm hb ((finiteSumEquiv μ).symm f)
  change (assemble μ (diagonalAmplification h (operator μ T hm hb)
    ((finiteSumEquiv μ).symm f))) =ᵐ[μ] _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [show assemble μ ((finiteSumEquiv μ).symm f)=f from (finiteSumEquiv μ).apply_symm_apply f]

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiberCommutator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma operator_commutator (T S : Ω → H →L[ℂ] H)
    (hT : ∀ ξ : H,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hS : ∀ ξ : H,AEStronglyMeasurable (fun a => S a ξ) μ)
    {b c : ℝ} (hb0 : 0≤b) (hc0 : 0 ≤ c)
    (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖S a‖ ≤ c) :
    operator μ T hT hb*operator μ S hS hc-operator μ S hS hc*operator μ T hT hb=
    operator μ (fun a => T a*S a-S a*T a) (commutator_measurable μ T S hT hS)
      (commutator_field_bound μ T S hb0 hc0 hb hc) := by
  apply operator_eq_of_ae_apply
  intro f
  filter_upwards [operator_ae μ T hT hb (operator μ S hS hc f),
    operator_ae μ S hS hc (operator μ T hT hb f),operator_ae μ T hT hb f,
    operator_ae μ S hS hc f,
    Lp.coeFn_sub (operator μ T hT hb (operator μ S hS hc f))
      (operator μ S hS hc (operator μ T hT hb f))] with a h1 h2 h3 h4 h5
  change (operator μ T hT hb (operator μ S hS hc f)-operator μ S hS hc (operator μ T hT hb f)) a=_
  rw [h5]
  change operator μ T hT hb (operator μ S hS hc f) a-
    operator μ S hS hc (operator μ T hT hb f) a=_
  rw [h1,h2,h3,h4]
  rfl

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixField
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma assemble_matrix_ae (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hm : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {b : Fin h → Fin h → ℝ} (hb : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤b i j)
    (f : PiLp 2 (fun _ : Fin h => Lp H 2 μ)) :
    assemble μ (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)) f)=ᵐ[μ]
    fun a => matrixOperator h (fun i j => X i j a) (assemble μ f a) := by
  have he : ∀ᵐ a ∂μ,∀ i j,operator μ (X i j) (hm i j) (hb i j) (f j) a=X i j a (f j a) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => operator_ae μ _ _ _ (f j)))
  have hs : ∀ᵐ a ∂μ,∀ i,(∑ j,operator μ (X i j) (hm i j) (hb i j) (f j)) a=
      ∑ j,operator μ (X i j) (hm i j) (hb i j) (f j) a :=
    ae_all_iff.mpr (fun i => Lp.coeFn_fun_finsetSum _ _)
  filter_upwards [assemble_ae μ (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)) f),
    assemble_ae μ f,he,hs] with a ha hf he hs
  rw [ha,hf]
  ext i
  change (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)) f i) a=
    matrixOperator h (fun i j => X i j a) (WithLp.toLp 2 (fun i => f i a)) i
  erw [matrixOperator_apply,matrixOperator_apply]
  rw [hs i]
  exact Finset.sum_congr rfl (fun j _ => he i j)

lemma matrix_conjugate (h : ℕ) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hm : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {b : Fin h → Fin h → ℝ} (hb : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖≤b i j) :
    (finiteSumEquiv μ).conjStarAlgEquiv
      (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j)))=
    operator μ (fun a => matrixOperator h (fun i j => X i j a))
      (matrix_field_measurable μ h X hm) (matrix_field_bound μ h X hb) := by
  apply operator_eq_of_ae_apply
  intro f
  have hh := assemble_matrix_ae μ h X hm hb ((finiteSumEquiv μ).symm f)
  change (assemble μ (matrixOperator h (fun i j => operator μ (X i j) (hm i j) (hb i j))
    ((finiteSumEquiv μ).symm f))) =ᵐ[μ] _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [show assemble μ ((finiteSumEquiv μ).symm f)=f from (finiteSumEquiv μ).apply_symm_apply f]

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryMainTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K)

lemma conj_norm (a : H →L[ℂ] H) : ‖U.conjStarAlgEquiv a‖=‖a‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
    intro x
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map]
      using a.le_opNorm (U.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map,
      U.symm_apply_apply] using (U.conjStarAlgEquiv a).le_opNorm (U x)

end Kadison.UnitaryTransport

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorFieldBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω : Type*} {H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem matrix_commutator_bound_of_factor_fields_oai
    (Q : Ω → VonNeumannAlgebra H) (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (T : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b d : ℝ} (hb0 : 0≤b) (hd : 0≤d) (hb : ∀ᵐ a ∂μ,‖T a‖≤b)
    (hg : ∀ᵐ a ∂μ,commutatorSeminorm (Q a) (T a)≤d)
    (h : ℕ) (hh : 1≤h) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hX : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {c : Fin h → Fin h → ℝ} (hc0 : ∀ i j,0 ≤ c i j)
    (hc : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖ ≤ c i j)
    (hmem : ∀ᵐ a ∂μ,∀ i j,X i j a∈Q a) :
    ‖diagonalAmplification h (operator μ T hT hb)*
        matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))-
      matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))*
        diagonalAmplification h (operator μ T hT hb)‖≤
      3122*d*‖matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))‖ := by
  let D := fun a => diagonalAmplification h (T a)
  let M := fun a => matrixOperator h (fun i j => X i j a)
  let G := matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))
  have hD := diagonal_field_measurable μ h T hT
  have hM := matrix_field_measurable μ h X hX
  have hDb := diagonal_field_bound μ h T hb
  have hMb := matrix_field_bound μ h X hc
  have hcnonneg : 0≤∑ i,∑ j,c i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hc0 i j))
  have hmatrix : ∀ᵐ a ∂μ,‖M a‖≤‖G‖ := by
    apply (operator_norm_le_iff_ae μ M hM hMb (norm_nonneg G)).mp
    rw [←matrix_conjugate μ h X hX hc,UnitaryTransport.conj_norm]
  have hfiber : ∀ᵐ a ∂μ,‖D a*M a-M a*D a‖≤3122*d*‖G‖ := by
    filter_upwards [hfac,hmem,hg,hmatrix] with a hfa hma hga hna
    have hf := uniform_commutator_separable_factor (Q a) hfa (T a) h hh
      (fun i j => X i j a) hma
    exact hf.trans (mul_le_mul (mul_le_mul_of_nonneg_left hga (by norm_num)) hna
      (norm_nonneg _) (mul_nonneg (by norm_num) hd))
  have hn := operator_norm_le μ (fun a => D a*M a-M a*D a)
    (commutator_measurable μ D M hD hM)
    (commutator_field_bound μ D M hb0 hcnonneg hDb hMb)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3122) hd) (norm_nonneg G)) hfiber
  rw [←operator_commutator μ D M hD hM hb0 hcnonneg hDb hMb] at hn
  change ‖operator μ D hD hDb*operator μ M hM hMb-
    operator μ M hM hMb*operator μ D hD hDb‖≤_ at hn
  rw [←diagonal_conjugate μ h T hT hb,←matrix_conjugate μ h X hX hc,
    ←map_mul,←map_mul,←map_sub,UnitaryTransport.conj_norm] at hn
  exact hn

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.Decomposable.matrix_commutator_bound_of_factor_fields_oai.{u_1} := @OAI.Kadison.Decomposable.matrix_commutator_bound_of_factor_fields_oai.{u_1}
