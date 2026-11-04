-- Prove2me | solution 1 for OAI.KadisonSimilarity.embedded_actions_adjoint_repeated_word
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:32:23.129409+00:00
-- url     : https://prove2.me/submissions/7e78b2bd-53ec-4187-bf81-676d8d6d1481

import Mathlib
import Definitions.Def_OAIQ075A037
import Theorems.Thm_OAI_KadisonSimilarity_adjoint_commutes_of_adjoint_commutes

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantCoefficients
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coefficient-vanishing steps in the invariant-tensor argument

These are the two limiting arguments in `lem:invariant-intertwiners`.
They do not assume the classification of intertwiners: the finite-stage
coefficient identities and their norm bounds still have to be constructed.
-/

noncomputable section

namespace KadisonSimilarity

open Filter
open scoped Topology

private theorem coefficient_zero_of_power_bound (m : ℕ → ℝ)
    (hm : ∀ j, 0 < m j) (hmTop : Tendsto m atTop atTop)
    {a C p q : ℝ} (hqp : q < p)
    (hbound : ∀ j, |a| * (m j) ^ p ≤ C * (m j) ^ q) : a = 0 := by
  have hle (j : ℕ) : |a| ≤ C * (m j) ^ (q - p) := by
    rw [Real.rpow_sub (hm j)]
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (hm j) p)).mpr (hbound j)
  have ht : Tendsto (fun j => C * (m j) ^ (q - p)) atTop (𝓝 0) := by
    have ht₀ := (tendsto_rpow_neg_atTop (sub_pos.mpr hqp)).comp hmTop
    have hsub : q - p = -(p - q) := by ring
    rw [hsub]
    simpa using ht₀.const_mul C
  have hnonpos : |a| ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hle)
  exact abs_eq_zero.mp (le_antisymm hnonpos (abs_nonneg a))

/-- The endpoint `L¹` bound removes a stable cycle coefficient whose number
of cycles is below `1 + (k+l)/2`. Matrix sizes may run through any cofinal
sequence, as they do for the increasing matrix subalgebras in the paper. -/
theorem cycle_coefficient_zero (m : ℕ → ℝ)
    (hm : ∀ j, 0 < m j) (hmTop : Tendsto m atTop atTop)
    (k l cycles : ℕ) (a : ℂ) (C : ℝ)
    (hfew : (cycles : ℝ) < 1 + ((k : ℝ) + l) / 2)
    (hbound : ∀ j, ‖a‖ * (m j) ^ (-(cycles : ℝ)) ≤
      C * (m j) ^ (-1 - ((k : ℝ) + l) / 2)) : a = 0 := by
  have hzero : ‖a‖ = 0 := by
    apply coefficient_zero_of_power_bound m hm hmTop (by linarith :
      -1 - ((k : ℝ) + l) / 2 < -(cycles : ℝ))
    simpa only [abs_norm] using hbound
  exact norm_eq_zero.mp hzero

/-- Summing orthonormal labels removes a pairing with a source-source or
test-test pair: its coefficient grows faster than the product of vector norms. -/
theorem same_side_pairing_coefficient_zero (a : ℂ) (C : ℝ) (rSource rTest : ℕ)
    (hpair : 0 < rSource + rTest)
    (hbound : ∀ M : ℕ, 0 < M →
      ‖a‖ * (M : ℝ) ^ ((rSource + rTest : ℕ) : ℝ) ≤
        C * (M : ℝ) ^ (((rSource + rTest : ℕ) : ℝ) / 2)) : a = 0 := by
  have hr : (0 : ℝ) < rSource + rTest := by exact_mod_cast hpair
  have hmTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hzero : ‖a‖ = 0 := by
    apply coefficient_zero_of_power_bound (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
      (by intro n; positivity) hmTop (by push_cast; linarith :
        (((rSource + rTest : ℕ) : ℝ) / 2) < ((rSource + rTest : ℕ) : ℝ))
    intro n
    simpa only [abs_norm] using hbound (n + 1) (by omega)
  exact norm_eq_zero.mp hzero

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantTensors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix-unit isolation of invariant-tensor coefficients

The permutation contractions are given by their coordinate sums. Their
normalization is the number of cycles, including fixed points. We prove the
matrix-unit isolation and uniqueness steps in the invariant-intertwiner
argument. Schur--Weyl spanning is expressed as a multilinear-form property.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [Fintype α] in
private theorem contraction_test_summand (j : ι → α) (hj : Function.Injective j)
    (π ρ : Equiv.Perm ι) (f : ι → α) :
    (∏ i, permutationTest j π i (f i) (f (ρ i))) =
      if f = j ∧ ρ = π then 1 else 0 := by
  classical
  by_cases hf : f = j
  · subst f
    by_cases hρ : ρ = π
    · subst ρ
      simp [permutationTest]
    · have hdiff : ∃ i, ρ i ≠ π i := by
        by_contra! h
        exact hρ (Equiv.ext h)
      obtain ⟨i, hi⟩ := hdiff
      simp only [hρ]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hij : j (ρ i) ≠ j (π i) := fun h => hi (hj h)
      simp [permutationTest, hij]
  · have hdiff : ∃ i, f i ≠ j i := by
      by_contra! h
      exact hf (funext h)
    obtain ⟨i, hi⟩ := hdiff
    simp only [hf, false_and, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [permutationTest, hi]

/-- A matrix-unit tuple isolates exactly its prescribed permutation. This
proves the independence assertion, independently of Schur--Weyl duality. -/
theorem permutationContraction_test (j : ι → α) (hj : Function.Injective j)
    (π ρ : Equiv.Perm ι) :
    permutationContraction ρ (permutationTest j π) = if ρ = π then 1 else 0 := by
  classical
  simp only [permutationContraction, contraction_test_summand j hj]
  by_cases hρ : ρ = π <;> simp [hρ]

theorem normalizedPermutationContraction_test
    (j : ι → α) (hj : Function.Injective j) (π ρ : Equiv.Perm ι) :
    normalizedPermutationContraction ρ (permutationTest j π) =
      if ρ = π then (Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π else 0 := by
  classical
  rw [normalizedPermutationContraction, permutationContraction_test j hj]
  split_ifs with h <;> simp [h]

/-- Evaluation at the associated matrix units recovers one coefficient of
any expansion in normalized permutation contractions. -/
theorem normalizedPermutationContraction_sum_test
    (j : ι → α) (hj : Function.Injective j) (π : Equiv.Perm ι)
    (c : Equiv.Perm ι → ℂ) :
    (∑ ρ, c ρ * normalizedPermutationContraction ρ (permutationTest j π)) =
      c π * (Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π := by
  classical
  simp [normalizedPermutationContraction_test j hj]

/-- In the stable range, expansion coefficients are unique. This is the
specific independence step needed when comparing nested matrix stages. -/
theorem normalizedPermutationContraction_coefficients_unique
    [Nonempty α] (j : ι → α) (hj : Function.Injective j)
    (c d : Equiv.Perm ι → ℂ)
    (heq : ∀ v : ι → Matrix α α ℂ,
      (∑ π, c π * normalizedPermutationContraction π v) =
        ∑ π, d π * normalizedPermutationContraction π v) : c = d := by
  funext π
  have h := heq (permutationTest j π)
  rw [normalizedPermutationContraction_sum_test j hj,
    normalizedPermutationContraction_sum_test j hj] at h
  exact mul_right_cancel₀ (pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr
    Fintype.card_ne_zero))) h

/-- The norm of the isolated coefficient has exactly the decay factor used
in the endpoint estimate. -/
theorem norm_normalizedPermutationContraction_sum_test
    (j : ι → α) (hj : Function.Injective j) (π : Equiv.Perm ι)
    (c : Equiv.Perm ι → ℂ) :
    ‖∑ ρ, c ρ * normalizedPermutationContraction ρ (permutationTest j π)‖ =
      ‖c π‖ * (Fintype.card α : ℝ) ^ (-(permutationCycleCount π : ℝ)) := by
  rw [normalizedPermutationContraction_sum_test j hj, norm_mul, norm_pow,
    norm_inv, Complex.norm_natCast, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

section BlockAmplification

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem card_cycleConstantLabelings (π : Equiv.Perm ι) :
    Fintype.card (CycleConstantLabelings π β) =
      Fintype.card β ^ permutationCycleCount π := by
  classical
  let : Fintype (Quotient (Equiv.Perm.SameCycle.setoid π)) := Fintype.ofFinite _
  rw [Fintype.card_congr (cycleConstantLabelingsEquiv (β := β) π), Fintype.card_fun]
  rw [permutationCycleCount, Nat.card_eq_fintype_card]

end BlockAmplification

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.MatrixHilbertStage.form_apply _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorPermutation_constant _root_.OAI.KadisonSimilarity.completedTensorPermutation_word _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.endpointAmplification_insert _root_.OAI.KadisonSimilarity.endpointHeadAction_insert _root_.OAI.KadisonSimilarity.endpointInsert_apply _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.endpointTensorMap_insert _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_endpointInsert _root_.OAI.KadisonSimilarity.inner_endpointWord _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.invariantStageForm_apply _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_endpointInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorPermutationLinear_word _root_.OAI.KadisonSimilarity.tensorWordLiftLinear_apply_word _root_.OAI.KadisonSimilarity.tensorWordMultilinear_apply _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite words in completed Hilbert tensor powers

The scalar word has length zero. Longer words are genuine Hilbert tensor
products, completed only after the finite algebraic tensor product is formed.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct
universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- All words formed from an orthonormal alphabet form an orthonormal family. -/
theorem orthonormal_completedTensorWords {J : Type*} (h : J → E) (hh : Orthonormal ℂ h)
    (n : ℕ) :
    Orthonormal ℂ (fun f : Fin n → J => completedTensorWord (fun i => h (f i))) := by
  classical
  rw [orthonormal_iff_ite]
  intro f g
  rw [inner_completedTensorWord]
  simp only [orthonormal_iff_ite.mp hh]
  by_cases hfg : f = g
  · subst g
    simp
  · have hex : ∃ i, f i ≠ g i := by
      by_contra! hc
      exact hfg (funext hc)
    obtain ⟨i, hi⟩ := hex
    simp only [hfg, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The sum of a finite orthonormal family has norm the square root of its
cardinality. This supplies the exact growth rate in the pairing test. -/
theorem norm_sum_orthonormal {H J : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Fintype J] (v : J → H) (hv : Orthonormal ℂ v) :
    ‖∑ j, v j‖ = Real.sqrt (Fintype.card J) := by
  classical
  have hi : inner ℂ (∑ j, v j) (∑ j, v j) = (Fintype.card J : ℂ) := by
    simp only [sum_inner, inner_sum, orthonormal_iff_ite.mp hv]
    simp
  have hs : ‖∑ j, v j‖ ^ 2 = (Fintype.card J : ℝ) := by
    rw [@norm_sq_eq_re_inner ℂ, hi]
    simp
  rw [← hs, Real.sqrt_sq_eq_abs, abs_norm]

/-- Vanishing simple-tensor coefficients force a completed tensor operator
to be zero. Both input and output totality are proved above. -/
theorem tensorOperator_eq_zero_of_word_coefficients {k l : ℕ}
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (hword : ∀ (x : Fin k → E) (y : Fin l → E),
      inner ℂ (completedTensorWord y) (Y (completedTensorWord x)) = 0) : Y = 0 := by
  apply continuousLinearMap_ext_completedTensorWords
  intro x
  have hlin : innerSL ℂ (Y (completedTensorWord x)) = 0 := by
    apply continuousLinearMap_ext_completedTensorWords
    intro y
    change inner ℂ (Y (completedTensorWord x)) (completedTensorWord y) = 0
    simpa only [inner_conj_symm, map_zero] using congrArg (starRingEnd ℂ) (hword x y)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have heq := congrArg (fun f : CompletedTensorWord E l →L[ℂ] ℂ =>
    f (Y (completedTensorWord x))) hlin
  change inner ℂ (Y (completedTensorWord x)) (Y (completedTensorWord x)) = 0 at heq
  exact heq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.MatrixHilbertStage.form_apply _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorPermutation_constant _root_.OAI.KadisonSimilarity.completedTensorPermutation_word _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.endpointAmplification_insert _root_.OAI.KadisonSimilarity.endpointHeadAction_insert _root_.OAI.KadisonSimilarity.endpointInsert_apply _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.endpointTensorMap_insert _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_endpointInsert _root_.OAI.KadisonSimilarity.inner_endpointWord _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.invariantStageForm_apply _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_endpointInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorPermutationLinear_word _root_.OAI.KadisonSimilarity.tensorWordLiftLinear_apply_word _root_.OAI.KadisonSimilarity.tensorWordMultilinear_apply _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The endpoint matrix-unit estimate from a supporting projection

For the coefficient tests it suffices to move a self-adjoint supporting
projection across the inner product. This gives the required dimension factor
without invoking the full tracial commutation theorem.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The normalized matrix-unit bound multiplies over all tensor letters. -/
theorem norm_completedTensorWord_le_matrix_units {n : ℕ} (x : Fin n → E)
    (m : ℝ) (hm : 0 < m) (hx : ∀ i, ‖x i‖ ≤ m ^ (-(1 : ℝ) / 2)) :
    ‖completedTensorWord x‖ ≤ m ^ (-(n : ℝ) / 2) := by
  rw [norm_completedTensorWord]
  calc
    _ ≤ ∏ _ : Fin n, m ^ (-(1 : ℝ) / 2) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx i)
    _ = (m ^ (-(1 : ℝ) / 2)) ^ n := by simp
    _ = m ^ (-(n : ℝ) / 2) := by
      rw [← Real.rpow_mul_natCast hm.le]
      congr 1
      ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantCycles
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.sourcePairClassDecidable _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassDecidable _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.crossPairingEquiv_left _root_.OAI.KadisonSimilarity.crossPairingEquiv_right _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing centered singleton cycles

A fixed point contributes the trace of its matrix argument. Factorization
of the coordinate contraction shows that vanishing on
centered singleton tails does not require an additional invariant-theory input.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- A fixed point contributes precisely an unnormalized trace factor. -/
theorem permutationContraction_fixedPoint (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) :
    permutationContraction π v = Matrix.trace (v i) * fixedPointRemainder π i hi v := by
  classical
  unfold permutationContraction fixedPointRemainder
  rw [Fintype.sum_equiv (Equiv.funSplitAt i α) _
    (fun fg => v i fg.1 fg.1 *
      ∏ j : {j : ι // j ≠ i}, v j (fg.2 j) (fg.2 (fixedPointComplement π i hi j)))]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul (Finset.univ : Finset α) (fun a => v i a a)
      (∑ g : {j : ι // j ≠ i} → α,
        ∏ j : {j : ι // j ≠ i}, v j (g j) (g (fixedPointComplement π i hi j)))]
    rfl
  · intro f
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [hi]
    rfl

/-- Any singleton cycle on a centered variable vanishes identically. -/
theorem permutationContraction_eq_zero_of_fixed_centered
    (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) (hcenter : Matrix.trace (v i) = 0) :
    permutationContraction π v = 0 := by
  rw [permutationContraction_fixedPoint π i hi, hcenter, zero_mul]

/-- The same deletion holds for the normalized cycle forms. -/
theorem normalizedPermutationContraction_eq_zero_of_fixed_centered
    (π : Equiv.Perm ι) (i : ι) (hi : π i = i)
    (v : ι → Matrix α α ℂ) (hcenter : Matrix.trace (v i) = 0) :
    normalizedPermutationContraction π v = 0 := by
  rw [normalizedPermutationContraction,
    permutationContraction_eq_zero_of_fixed_centered π i hi v hcenter, mul_zero]

omit [DecidableEq ι] in
/-- Cycle lengths sum to the number of slots. -/
theorem sum_cycleLengths (π : Equiv.Perm ι) :
    (∑ q : PermutationCycles π, Fintype.card (CycleMembers π q)) = Fintype.card ι := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun i : ι =>
    (⟦i⟧ : PermutationCycles π)))

omit [DecidableEq ι] in
theorem card_permutationCycles (π : Equiv.Perm ι) :
    Fintype.card (PermutationCycles π) = permutationCycleCount π := by
  exact (Nat.card_eq_fintype_card).symm

omit [DecidableEq ι] in
theorem cycleLength_pos (π : Equiv.Perm ι) (q : PermutationCycles π) :
    0 < Fintype.card (CycleMembers π q) := by
  obtain ⟨i, hi⟩ := Quotient.exists_rep q
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

omit [DecidableEq ι] in
/-- A cycle containing no fixed point has at least two vertices. -/
theorem two_le_cycleLength (π : Equiv.Perm ι) (q : PermutationCycles π)
    (hfixed : ∀ i, (⟦i⟧ : PermutationCycles π) = q → π i ≠ i) :
    2 ≤ Fintype.card (CycleMembers π q) := by
  obtain ⟨i, hi⟩ := Quotient.exists_rep q
  have hπ : (⟦π i⟧ : PermutationCycles π) = q :=
    (Quotient.sound (show π.SameCycle (π i) i from
      (show π.SameCycle i (π i) from ⟨1, by simp⟩).symm)).trans hi
  have hne : (⟨i, hi⟩ : CycleMembers π q) ≠ ⟨π i, hπ⟩ := by
    intro h
    exact hfixed i hi (congrArg Subtype.val h).symm
  exact Fintype.one_lt_card_iff.mpr ⟨⟨i, hi⟩, ⟨π i, hπ⟩, hne⟩

/-- The cycle threshold forces the distinguished endpoint to be fixed. The
only other assumption is the already justified removal of tail singletons. -/
theorem cycle_threshold_fixes_endpoint (π : Equiv.Perm ι) (i₀ : ι)
    (hfixed : ∀ i, π i = i → i = i₀)
    (hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π) : π i₀ = i₀ := by
  classical
  by_contra h₀
  have hno : ∀ i, π i ≠ i := by
    intro i hi
    have hieq := hfixed i hi
    subst i
    exact h₀ hi
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (f := fun _ : PermutationCycles π => 2)
    (g := fun q => Fintype.card (CycleMembers π q))
    (fun q _ => two_le_cycleLength π q (fun i _ => hno i))
  rw [sum_cycleLengths] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_permutationCycles] at hsum
  omega

private theorem sum_endpoint_weights {Q : Type*} [Fintype Q] [DecidableEq Q] (q₀ : Q) :
    (∑ q : Q, if q = q₀ then 1 else 2) + 1 = 2 * Fintype.card Q := by
  have hc : Fintype.card {q : Q // q ≠ q₀} + 1 = Fintype.card Q := by
    simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe q₀)
  rw [Fintype.sum_eq_add_sum_subtype_ne _ q₀]
  have hs : (∑ q : {q : Q // q ≠ q₀}, if (q : Q) = q₀ then 1 else 2) =
      Fintype.card {q : Q // q ≠ q₀} * 2 := by
    calc
      _ = ∑ _q : {q : Q // q ≠ q₀}, 2 :=
        Finset.sum_congr rfl (fun q _ => ite_eq_right q.2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hs]
  simp only [ite_true]
  omega

omit [DecidableEq ι] in
/-- At the threshold, every nondistinguished cycle has length two. -/
theorem cycle_threshold_lengths (π : Equiv.Perm ι) (i₀ : ι)
    (hfixed : ∀ i, π i = i → i = i₀)
    (hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π) :
    ∀ q : PermutationCycles π,
      Fintype.card (CycleMembers π q) = if q = ⟦i₀⟧ then 1 else 2 := by
  classical
  have hle (q : PermutationCycles π) :
      (if q = ⟦i₀⟧ then 1 else 2) ≤ Fintype.card (CycleMembers π q) := by
    split_ifs with hq
    · exact cycleLength_pos π q
    · apply two_le_cycleLength
      intro i hi hfix
      have hieq := hfixed i hfix
      subst i
      exact hq hi.symm
  have htotal : (∑ q : PermutationCycles π, if q = ⟦i₀⟧ then 1 else 2) =
      Fintype.card ι := by
    have hs := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hle q)
    rw [sum_cycleLengths] at hs
    have hb := sum_endpoint_weights (⟦i₀⟧ : PermutationCycles π)
    rw [card_permutationCycles] at hb
    exact Nat.le_antisymm hs (Nat.le_of_add_le_add_right (hcount.trans_eq hb.symm))
  intro q
  apply le_antisymm ?_ (hle q)
  by_contra h
  have hlt := Finset.sum_lt_sum
    (fun q (_ : q ∈ Finset.univ) => hle q)
    ⟨q, Finset.mem_univ q, Nat.lt_of_not_ge h⟩
  rw [sum_cycleLengths, htotal] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- If all permutation cycles have at most two elements, the permutation is
an involution. This follows by putting three successive vertices in one fiber. -/
theorem involutive_of_cycleLengths_le_two (π : Equiv.Perm ι)
    (hsize : ∀ q : PermutationCycles π, Fintype.card (CycleMembers π q) ≤ 2) :
    Function.Involutive π := by
  intro i
  by_contra hbad
  have heq (i : ι) : (⟦π i⟧ : PermutationCycles π) = ⟦i⟧ :=
    Quotient.sound ((show π.SameCycle i (π i) from ⟨1, by simp⟩).symm)
  let a : CycleMembers π (⟦i⟧ : PermutationCycles π) := ⟨i, rfl⟩
  let b : CycleMembers π (⟦i⟧ : PermutationCycles π) := ⟨π i, heq i⟩
  let c : CycleMembers π (⟦i⟧ : PermutationCycles π) :=
    ⟨π (π i), (heq (π i)).trans (heq i)⟩
  have hcollapse (h : i = π i) : π (π i) = i :=
    (congrArg π h.symm).trans h.symm
  have hab : a ≠ b := fun h => hbad (hcollapse (congrArg Subtype.val h))
  have hac : a ≠ c := fun h => hbad (congrArg Subtype.val h).symm
  have hbc : b ≠ c := fun h =>
    hbad (hcollapse (π.injective (congrArg Subtype.val h)))
  have ht : 2 < Fintype.card (CycleMembers π (⟦i⟧ : PermutationCycles π)) := by
    simpa only [Finset.card_univ] using
      (Finset.two_lt_card_iff.mpr ⟨a, b, c, Finset.mem_univ _, Finset.mem_univ _,
        Finset.mem_univ _, hab, hac, hbc⟩ :
        2 < (Finset.univ : Finset (CycleMembers π (⟦i⟧ : PermutationCycles π))).card)
  exact (not_lt_of_ge (hsize _) ht)

/-- The surviving cycle structures are precisely an endpoint singleton and
a fixed-point-free involution on the tail slots. -/
theorem cycle_threshold_pairing (π : Equiv.Perm ι) (i₀ : ι)
    (hfixed : ∀ i, π i = i → i = i₀)
    (hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π) :
    π i₀ = i₀ ∧ Function.Involutive π ∧ ∀ i, i ≠ i₀ → π i ≠ i := by
  refine ⟨cycle_threshold_fixes_endpoint π i₀ hfixed hcount, ?_, ?_⟩
  · apply involutive_of_cycleLengths_le_two
    intro q
    rw [cycle_threshold_lengths π i₀ hfixed hcount]
    split_ifs <;> omega
  · intro i hne hi
    exact hne (hfixed i hi)

/-- Combining coefficient decay with centered-singleton deletion reduces the
finite invariant expansion to pairings of all tail slots. The coefficient
vanishing premise is supplied by the proved matrix-test limit theorem. -/
theorem invariant_expansion_reduce_to_pairings
    (i₀ : ι) (v : ι → Matrix α α ℂ)
    (hcenter : ∀ i, i ≠ i₀ → Matrix.trace (v i) = 0)
    (c : Equiv.Perm ι → ℂ)
    (hsmall : ∀ π, 2 * permutationCycleCount π < Fintype.card ι + 1 → c π = 0) :
    (∑ π, c π * normalizedPermutationContraction π v) =
      ∑ π ∈ Finset.univ.filter (fun π => EndpointPairing π i₀),
        c π * normalizedPermutationContraction π v := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro π _ hπ
  by_cases htail : ∀ i, π i = i → i = i₀
  · by_cases hcount : Fintype.card ι + 1 ≤ 2 * permutationCycleCount π
    · obtain ⟨hfix, hinv, _⟩ := cycle_threshold_pairing π i₀ htail hcount
      exact False.elim (hπ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfix, hinv, htail⟩))
    · rw [hsmall π (Nat.lt_of_not_ge hcount), zero_mul]
  · have hex : ∃ i, π i = i ∧ i ≠ i₀ := by
      by_contra hn
      apply htail
      intro i hi
      by_contra hne
      exact hn ⟨i, hi, hne⟩
    obtain ⟨i, hi, hne⟩ := hex
    rw [normalizedPermutationContraction_eq_zero_of_fixed_centered π i hi v (hcenter i hne),
      mul_zero]

/-- Cross pairings exist only when the source and test degrees coincide. -/
theorem degrees_eq_of_crossPairing {k l : ℕ} (π : Equiv.Perm (Fin k ⊕ Fin l))
    (hπ : Function.Involutive π) (hcross : IsCrossPairing π) : k = l := by
  simpa using Fintype.card_congr (crossPairingEquiv π hπ hcross)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_PairingLabels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.crossPairingEquiv_left _root_.OAI.KadisonSimilarity.crossPairingEquiv_right _root_.OAI.KadisonSimilarity.endpointMatchingEquiv_apply _root_.OAI.KadisonSimilarity.endpointMatching_none _root_.OAI.KadisonSimilarity.endpointMatching_some _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.matchingSplitEquiv_inl _root_.OAI.KadisonSimilarity.matchingSplitEquiv_inr _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disjoint labels for the pairing test

The cycle classes of one perfect matching index disjoint label pools. This
isolates that matching while allowing the labels of same-side pairs to vary.
-/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A cycle of a matching has exactly its two paired vertices. -/
theorem sameCycle_perfectMatching_iff (P : PerfectMatching ι) (i j : ι) :
    P.1.SameCycle i j ↔ j = i ∨ j = P.1 i := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h
        · exact Or.inr (congrArg P.1 h)
        · exact Or.inl ((congrArg P.1 h).trans (P.2.1 i))
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simp⟩

/-- Labels identifying exactly the pairs of `P` kill every other matching. -/
theorem pairingLabelKernel_isolate {J : Type*} [DecidableEq J]
    (P Q : PerfectMatching ι) (labels : ι → J)
    (hlabels : ∀ i j, labels i = labels j ↔ j = i ∨ j = P.1 i) :
    pairingLabelKernel Q labels = if Q = P then 1 else 0 := by
  classical
  by_cases hQP : Q = P
  · subst Q
    simp only [pairingLabelKernel, ite_true]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left ((hlabels i (P.1 i)).mpr (Or.inr rfl))
  · have hex : ∃ i, Q.1 i ≠ P.1 i := by
      by_contra! h
      exact hQP (Subtype.ext (Equiv.ext h))
    obtain ⟨i, hi⟩ := hex
    have hne : labels i ≠ labels (Q.1 i) := by
      intro h
      rcases (hlabels i (Q.1 i)).mp h with h | h
      · exact Q.2.2 i h
      · exact hi h
    simp only [hQP, ↓reduceIte, pairingLabelKernel]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hne)

variable {k l : ℕ}

theorem sourcePairLabels_injective (P : PerfectMatching (Fin k ⊕ Fin l)) (M : ℕ) :
    Function.Injective (sourcePairLabels P (M := M)) := by
  intro f g hfg
  funext q
  rcases q with ⟨q, hq⟩
  obtain ⟨s, hs⟩ := Quotient.exists_rep q
  cases s with
  | inr j => exact False.elim (hq j hs)
  | inl i =>
      subst q
      have h := congrArg (fun z => (z i).2) hfg
      apply Fin.ext
      simpa [sourcePairLabels, hq] using h

theorem testPairLabels_injective (P : PerfectMatching (Fin k ⊕ Fin l)) (M : ℕ) :
    Function.Injective (testPairLabels P (M := M)) := by
  intro f g hfg
  funext q
  rcases q with ⟨q, hq⟩
  obtain ⟨s, hs⟩ := Quotient.exists_rep q
  cases s with
  | inl i => exact False.elim (hq i hs)
  | inr j =>
      subst q
      have h := congrArg (fun z => (z j).2) hfg
      apply Fin.ext
      simpa [testPairLabels, hq] using h

private theorem allPairLabels_source (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M) (i : Fin k) :
    allPairLabels P f g (Sum.inl i) = sourcePairLabels P f i := by
  have hn : ¬ IsTestPairClass P (⟦Sum.inl i⟧ : PermutationCycles P.1) := fun h => h i rfl
  simp only [allPairLabels, sourcePairLabels, hn, ↓reduceDIte]

private theorem allPairLabels_test (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M) (j : Fin l) :
    allPairLabels P f g (Sum.inr j) = testPairLabels P g j := by
  have hn : ¬ IsSourcePairClass P (⟦Sum.inr j⟧ : PermutationCycles P.1) := fun h => h j rfl
  simp only [allPairLabels, testPairLabels, hn, ↓reduceDIte]

/-- The combined source and test tuples identify exactly the chosen pairs. -/
theorem pairLabels_eq_iff (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M)
    (s t : Fin k ⊕ Fin l) :
    Sum.elim (sourcePairLabels P f) (testPairLabels P g) s =
        Sum.elim (sourcePairLabels P f) (testPairLabels P g) t ↔
      t = s ∨ t = P.1 s := by
  have heq (s : Fin k ⊕ Fin l) :
      Sum.elim (sourcePairLabels P f) (testPairLabels P g) s = allPairLabels P f g s := by
    cases s with
    | inl i => exact (allPairLabels_source P f g i).symm
    | inr j => exact (allPairLabels_test P f g j).symm
  rw [heq s, heq t, ← sameCycle_perfectMatching_iff P s t]
  constructor
  · intro h
    exact Quotient.exact (congrArg Prod.fst h)
  · intro h
    have he : (⟦s⟧ : PermutationCycles P.1) = ⟦t⟧ := Quotient.sound h
    simp only [allPairLabels, he]

/-- A source-source pair supplies a source-only cycle class. -/
theorem sourcePairClass_of_source_pair (P : PerfectMatching (Fin k ⊕ Fin l))
    (i i' : Fin k) (hp : P.1 (Sum.inl i) = Sum.inl i') :
    IsSourcePairClass P (⟦Sum.inl i⟧ : PermutationCycles P.1) := by
  intro j hq
  have hc := (sameCycle_perfectMatching_iff P (Sum.inl i) (Sum.inr j)).mp
    (Quotient.exact hq.symm)
  rcases hc with h | h <;> simp [hp] at h

/-- The analogous implication for a test-test pair. -/
theorem testPairClass_of_test_pair (P : PerfectMatching (Fin k ⊕ Fin l))
    (j j' : Fin l) (hp : P.1 (Sum.inr j) = Sum.inr j') :
    IsTestPairClass P (⟦Sum.inr j⟧ : PermutationCycles P.1) := by
  intro i hq
  have hc := (sameCycle_perfectMatching_iff P (Sum.inr j) (Sum.inl i)).mp
    (Quotient.exact hq.symm)
  rcases hc with h | h <;> simp [hp] at h

/-- If there are no same-side cycle classes, every pair crosses the two sides. -/
theorem isCrossPairing_of_no_same_side (P : PerfectMatching (Fin k ⊕ Fin l))
    (hS : Fintype.card (SourcePairClasses P) = 0)
    (hT : Fintype.card (TestPairClasses P) = 0) : IsCrossPairing P.1 := by
  have : IsEmpty (SourcePairClasses P) := Fintype.card_eq_zero_iff.mp hS
  have : IsEmpty (TestPairClasses P) := Fintype.card_eq_zero_iff.mp hT
  constructor
  · intro i
    cases hp : P.1 (Sum.inl i) with
    | inr j => exact ⟨j, rfl⟩
    | inl i' => exact isEmptyElim (⟨_, sourcePairClass_of_source_pair P i i' hp⟩ : SourcePairClasses P)
  · intro j
    cases hp : P.1 (Sum.inr j) with
    | inl i => exact ⟨i, rfl⟩
    | inr j' => exact isEmptyElim (⟨_, testPairClass_of_test_pair P j j' hp⟩ : TestPairClasses P)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.MatrixHilbertStage.form_apply _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorPermutation_constant _root_.OAI.KadisonSimilarity.completedTensorPermutation_word _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.crossPairingEquiv_left _root_.OAI.KadisonSimilarity.crossPairingEquiv_right _root_.OAI.KadisonSimilarity.endpointAmplification_insert _root_.OAI.KadisonSimilarity.endpointHeadAction_insert _root_.OAI.KadisonSimilarity.endpointInsert_apply _root_.OAI.KadisonSimilarity.endpointMatchingEquiv_apply _root_.OAI.KadisonSimilarity.endpointMatching_none _root_.OAI.KadisonSimilarity.endpointMatching_some _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.endpointTensorMap_insert _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_endpointInsert _root_.OAI.KadisonSimilarity.inner_endpointWord _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.invariantStageForm_apply _root_.OAI.KadisonSimilarity.matchingSplitEquiv_inl _root_.OAI.KadisonSimilarity.matchingSplitEquiv_inr _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_endpointInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorPermutationLinear_word _root_.OAI.KadisonSimilarity.tensorWordLiftLinear_apply_word _root_.OAI.KadisonSimilarity.tensorWordMultilinear_apply _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert tensor tests excluding same-side pairings

The source and test vectors are finite sums of actual elementary Hilbert
tensors. Their orthonormal summands give the square-root norm growth, whereas
the isolated pairing coefficient grows with the full number of labels.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {k l : ℕ}

/-- Relabeling an orthonormal alphabet by an injection preserves the formula. -/
theorem LabelPairingExpansion.comp {I J : Type*} [DecidableEq I] [DecidableEq J]
    {Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l}
    {h : J → E} {c : PerfectMatching (Fin k ⊕ Fin l) → ℂ}
    (hexp : LabelPairingExpansion Y h c) (f : I → J) (hf : Function.Injective f) :
    LabelPairingExpansion Y (h ∘ f) c := by
  intro s t
  change inner ℂ (completedTensorWord (fun i => h ((f ∘ t) i)))
    (Y (completedTensorWord (fun i => h ((f ∘ s) i)))) = _
  rw [hexp (f ∘ s) (f ∘ t)]
  apply Finset.sum_congr rfl
  intro Q _
  congr 1
  unfold pairingLabelKernel
  apply Finset.prod_congr rfl
  intro i _
  have heq (i : Fin k ⊕ Fin l) : Sum.elim (f ∘ s) (f ∘ t) i = f (Sum.elim s t i) := by
    cases i <;> rfl
  simp only [heq, hf.eq_iff]

theorem norm_sourcePairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (hh : Orthonormal ℂ h) (M : ℕ) :
    ‖sourcePairingTest P h M‖ = Real.sqrt ((M : ℝ) ^ Fintype.card (SourcePairClasses P)) := by
  have ho := (orthonormal_completedTensorWords h hh k).comp
    (sourcePairLabels P (M := M)) (sourcePairLabels_injective P M)
  simpa [sourcePairingTest, Function.comp_def, Fintype.card_fun] using norm_sum_orthonormal _ ho

theorem norm_testPairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (hh : Orthonormal ℂ h) (M : ℕ) :
    ‖testPairingTest P h M‖ = Real.sqrt ((M : ℝ) ^ Fintype.card (TestPairClasses P)) := by
  have ho := (orthonormal_completedTensorWords h hh l).comp
    (testPairLabels P (M := M)) (testPairLabels_injective P M)
  simpa [testPairingTest, Function.comp_def, Fintype.card_fun] using norm_sum_orthonormal _ ho

private theorem pairingExpansion_label_test
    (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ) :
    (∑ Q, c Q * pairingLabelKernel Q
      (Sum.elim (sourcePairLabels P f) (testPairLabels P g))) = c P := by
  classical
  simp [pairingLabelKernel_isolate P _ _ (pairLabels_eq_iff P f g)]

/-- Every summand contributes the same isolated coefficient. -/
theorem inner_pairingTests
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (P : PerfectMatching (Fin k ⊕ Fin l)) (h : PermutationCycles P.1 × ℕ → E)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (M : ℕ) :
    inner ℂ (testPairingTest P h M) (Y (sourcePairingTest P h M)) =
      c P * (M : ℂ) ^ (Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P)) := by
  classical
  unfold LabelPairingExpansion at hexp
  simp only [sourcePairingTest, testPairingTest, map_sum, sum_inner, inner_sum]
  simp_rw [hexp, pairingExpansion_label_test P]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]
  rw [pow_add]
  ring

private theorem sqrt_power_product (M a b : ℕ) :
    Real.sqrt ((M : ℝ) ^ a) * Real.sqrt ((M : ℝ) ^ b) =
      (M : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) := by
  rw [← Real.sqrt_mul (by positivity), ← pow_add, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The isolated coefficient grows as M^(rS+rT), while the two actual tensor
norms grow as M^((rS+rT)/2). -/
theorem pairing_coefficient_growth_bound
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (P : PerfectMatching (Fin k ⊕ Fin l)) (h : PermutationCycles P.1 × ℕ → E)
    (hh : Orthonormal ℂ h) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (M : ℕ) :
    ‖c P‖ * (M : ℝ) ^ ((Fintype.card (SourcePairClasses P) +
      Fintype.card (TestPairClasses P) : ℕ) : ℝ) ≤
      ‖Y‖ * (M : ℝ) ^ (((Fintype.card (SourcePairClasses P) +
        Fintype.card (TestPairClasses P) : ℕ) : ℝ) / 2) := by
  have hbound : ‖inner ℂ (testPairingTest P h M) (Y (sourcePairingTest P h M))‖ ≤
      ‖Y‖ * (‖sourcePairingTest P h M‖ * ‖testPairingTest P h M‖) := by
    calc
      _ ≤ ‖testPairingTest P h M‖ * ‖Y (sourcePairingTest P h M)‖ := norm_inner_le_norm _ _
      _ ≤ ‖testPairingTest P h M‖ * (‖Y‖ * ‖sourcePairingTest P h M‖) :=
        mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  rw [inner_pairingTests Y P h c hexp M, norm_mul, norm_pow, Complex.norm_natCast,
    norm_sourcePairingTest P h hh M, norm_testPairingTest P h hh M,
    sqrt_power_product] at hbound
  simpa only [Real.rpow_natCast] using hbound

/-- Boundedness excludes any coefficient with a same-side pair. -/
theorem same_side_pairing_coefficient_eq_zero
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (P : PerfectMatching (Fin k ⊕ Fin l)) (h : PermutationCycles P.1 × ℕ → E)
    (hh : Orthonormal ℂ h) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c)
    (hpair : 0 < Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P)) :
    c P = 0 := by
  apply same_side_pairing_coefficient_zero (c P) ‖Y‖
    (Fintype.card (SourcePairClasses P)) (Fintype.card (TestPairClasses P)) hpair
  intro M _
  exact pairing_coefficient_growth_bound Y P h hh c hexp M

theorem cyclePoolIndex_injective (P : PerfectMatching (Fin k ⊕ Fin l)) :
    Function.Injective (cyclePoolIndex P) := by
  intro a b hab
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.mp hab
  apply Prod.ext ?_ h₂
  exact (Fintype.equivFin _).injective (Fin.ext h₁)

/-- A single infinite orthonormal family suffices for all matching tests. -/
theorem same_side_pairing_coefficient_eq_zero_of_sequence
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : ℕ → E) (hh : Orthonormal ℂ h)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (P : PerfectMatching (Fin k ⊕ Fin l))
    (hpair : 0 < Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P)) :
    c P = 0 :=
  same_side_pairing_coefficient_eq_zero Y P (h ∘ cyclePoolIndex P)
    (hh.comp _ (cyclePoolIndex_injective P)) c
    (hexp.comp _ (cyclePoolIndex_injective P)) hpair

/-- Every nonzero coefficient must join source slots to test slots. -/
theorem nonzero_pairing_coefficient_isCrossPairing
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : ℕ → E) (hh : Orthonormal ℂ h)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (P : PerfectMatching (Fin k ⊕ Fin l))
    (hc : c P ≠ 0) : IsCrossPairing P.1 := by
  have hz : Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P) = 0 := by
    by_contra hn
    exact hc (same_side_pairing_coefficient_eq_zero_of_sequence Y h hh c hexp P
      (Nat.pos_of_ne_zero hn))
  exact isCrossPairing_of_no_same_side P (by omega) (by omega)

/-- In unequal degrees every pairing coefficient vanishes. -/
theorem pairing_coefficients_zero_of_degrees_ne
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : ℕ → E) (hh : Orthonormal ℂ h)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (hkl : k ≠ l) : c = 0 := by
  funext P
  by_contra hc
  exact hkl (degrees_eq_of_crossPairing P.1 P.2.1
    (nonzero_pairing_coefficient_isCrossPairing Y h hh c hexp P hc))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Passing finite-stage pairing identities to completed tensor words

Continuity and density extend the coefficient identity on a common matrix
stage to arbitrary letters. The final vanishing statement then uses actual
totality of elementary Hilbert tensors.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
/-- Finitely many letters in the union of nested stages lie in a common stage. -/
theorem exists_common_stage {ι : Type*} [Fintype ι]
    (S : ℕ → Set E) (hmono : Monotone S) (x : ι → E)
    (hx : ∀ i, x i ∈ ⋃ n, S n) : ∃ n, ∀ i, x i ∈ S n := by
  classical
  have hstage : ∀ i, ∃ n, x i ∈ S n := fun i => Set.mem_iUnion.mp (hx i)
  choose stage hstage using hstage
  refine ⟨Finset.univ.sup stage, fun i => ?_⟩
  exact hmono (Finset.le_sup (Finset.mem_univ i)) (hstage i)

omit [InnerProductSpace ℂ E] in
/-- Equality of continuous finite-letter functions on every common stage
extends to all letters. No coefficient identity is assumed outside the stages. -/
theorem continuous_eq_of_nested_stages {ι : Type*} [Fintype ι]
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ n, S n))
    (F G : (ι → E) → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hstage : ∀ n, ∀ x : ι → E, (∀ i, x i ∈ S n) → F x = G x) : F = G := by
  let U : Set E := ⋃ n, S n
  have hd : DenseRange (Pi.map (fun _ : ι => ((↑) : U → E))) :=
    DenseRange.piMap (fun _ => hdense.denseRange_val)
  apply hd.equalizer hF hG
  funext x
  obtain ⟨n, hn⟩ := exists_common_stage S hmono (fun i => (x i : E)) (fun i => (x i).property)
  exact hstage n _ hn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem continuous_pairingPolynomial (rank : ι → ℕ) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (P : PerfectMatching ι) : Continuous (pairingPolynomial rank B P) := by
  unfold pairingPolynomial
  fun_prop

omit [DecidableEq ι] in
/-- On a bilinearly orthonormal alphabet, the pairing polynomial is exactly
the equality-indicator kernel used by the Hilbert tensor tests. -/
theorem pairingPolynomial_labels {J : Type*} [DecidableEq J]
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (B : E →L[ℂ] E →L[ℂ] ℂ) (h : J → E)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (P : PerfectMatching ι) (labels : ι → J) :
    pairingPolynomial rank B P (fun i => h (labels i)) = pairingLabelKernel P labels := by
  classical
  unfold pairingPolynomial pairingLabelKernel
  simp only [hB]
  by_cases hall : ∀ i, labels i = labels (P.1 i)
  · have hright : (∏ i, if labels i = labels (P.1 i) then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one (fun i _ => ite_eq_left (hall i))
    rw [hright]
    exact Finset.prod_eq_one (fun i _ => ite_eq_left (hall i))
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hzero : (∏ i, if labels i = labels (P.1 i) then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    rw [hzero]
    have hneq : rank i ≠ rank (P.1 i) := fun he => P.2.2 i (hrank he).symm
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
        (ite_eq_right hi)
    · apply Finset.prod_eq_zero (i := P.1 i)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [P.2.1 i] using hgt⟩
      · simpa only [P.2.1 i] using (ite_eq_right (Ne.symm hi) :
          (if labels (P.1 i) = labels i then (1 : ℂ) else 0) = 0)

variable {k l : ℕ}

theorem continuous_tracialWordCoefficient
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (hJ : Continuous J) : Continuous (tracialWordCoefficient Y J) := by
  unfold tracialWordCoefficient
  apply Continuous.inner
  · apply (continuous_completedTensorWord l).comp
    exact continuous_pi (fun j => hJ.comp (continuous_apply (Sum.inr j)))
  · apply Y.continuous.comp
    apply (continuous_completedTensorWord k).comp
    exact continuous_pi (fun i => continuous_apply (Sum.inl i))

/-- The finite-stage coefficient formula extends by density, with no bounded
pairing operator presupposed. Each individual pairing polynomial is continuous
as a function of its finitely many letters. -/
theorem tracial_pairing_identity_of_stages
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (hJ : Continuous J)
    (B : E →L[ℂ] E →L[ℂ] ℂ) (rank : Fin k ⊕ Fin l → ℕ)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ n, S n))
    (hstage : ∀ n, ∀ v : Fin k ⊕ Fin l → E, (∀ i, v i ∈ S n) →
      tracialWordCoefficient Y J v = ∑ P, c P * pairingPolynomial rank B P v) :
    ∀ v : Fin k ⊕ Fin l → E,
      tracialWordCoefficient Y J v = ∑ P, c P * pairingPolynomial rank B P v := by
  classical
  have heq := continuous_eq_of_nested_stages S hmono hdense
    (tracialWordCoefficient Y J) (fun v => ∑ P, c P * pairingPolynomial rank B P v)
    (continuous_tracialWordCoefficient Y J hJ)
    (continuous_finsetSum _ (fun P _ => continuous_const.mul
      (continuous_pairingPolynomial rank B P))) hstage
  exact congrFun heq

/-- Restricting the extended stage identity to self-adjoint orthonormal
letters gives the precise input for the completed tensor label sums. -/
theorem labelPairingExpansion_of_tracial_identity
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (rank : Fin k ⊕ Fin l → ℕ) (hrank : Function.Injective rank)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ) (h : ℕ → E)
    (hJ : ∀ n, J (h n) = h n)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (hfull : ∀ v, tracialWordCoefficient Y J v =
      ∑ P, c P * pairingPolynomial rank B P v) : LabelPairingExpansion Y h c := by
  intro s t
  have heq := hfull (Sum.elim (fun i => h (s i)) (fun j => h (t j)))
  simp only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr, hJ] at heq
  rw [heq]
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  rw [show Sum.elim (fun i => h (s i)) (fun j => h (t j)) =
    (fun i => h (Sum.elim s t i)) from funext (fun i => by cases i <;> rfl)]
  exact pairingPolynomial_labels rank hrank B h hB P (Sum.elim s t)

/-- In unequal degrees, the stage formula, density, and orthonormal label
tests force the actual completed tensor operator to vanish. -/
theorem tensorOperator_eq_zero_of_tracial_stages
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (J : E → E) (hJ : Continuous J) (hJJ : Function.Involutive J)
    (B : E →L[ℂ] E →L[ℂ] ℂ)
    (rank : Fin k ⊕ Fin l → ℕ) (hrank : Function.Injective rank)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (h : ℕ → E) (hh : Orthonormal ℂ h) (hfix : ∀ n, J (h n) = h n)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ n, S n))
    (hstage : ∀ n, ∀ v : Fin k ⊕ Fin l → E, (∀ i, v i ∈ S n) →
      tracialWordCoefficient Y J v = ∑ P, c P * pairingPolynomial rank B P v)
    (hkl : k ≠ l) : Y = 0 := by
  have hfull := tracial_pairing_identity_of_stages Y J hJ B rank c S hmono hdense hstage
  have hlab := labelPairingExpansion_of_tracial_identity Y J B rank hrank c h hfix hB hfull
  have hc := pairing_coefficients_zero_of_degrees_ne Y h hh c hlab hkl
  apply tensorOperator_eq_zero_of_word_coefficients
  intro x y
  have heq := hfull (Sum.elim x (J ∘ y))
  have hJJ' (z : E) : J (J z) = z := hJJ z
  simpa only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    hJJ', hc, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using heq

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.MatrixHilbertStage.form_apply _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.endpointAmplification_insert _root_.OAI.KadisonSimilarity.endpointHeadAction_insert _root_.OAI.KadisonSimilarity.endpointInsert_apply _root_.OAI.KadisonSimilarity.endpointMatchingEquiv_apply _root_.OAI.KadisonSimilarity.endpointMatching_none _root_.OAI.KadisonSimilarity.endpointMatching_some _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.endpointTensorMap_insert _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_endpointInsert _root_.OAI.KadisonSimilarity.inner_endpointWord _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.invariantStageForm_apply _root_.OAI.KadisonSimilarity.matchingSplitEquiv_inl _root_.OAI.KadisonSimilarity.matchingSplitEquiv_inr _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_endpointInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From finite-stage pairings to permutation operators

The operator classification follows from the finite-stage coefficient
identity, using density, same-side-pair elimination, and completed tensor
permutations. The finite-stage identity remains a separately stated prerequisite.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem sourceFirstRank_injective {k l : ℕ} :
    Function.Injective (@sourceFirstRank k l) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (Fin.ext hab)
    | inr j => simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr] at hab; omega
  | inr i =>
    cases b with
    | inl j => simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr] at hab; omega
    | inr j =>
      simp only [sourceFirstRank, Sum.elim_inr] at hab
      exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hab))

/-- For a cross pairing, the full polynomial has exactly one factor per source slot. -/
theorem pairingPolynomial_cross {k l : ℕ}
    (B : E →L[ℂ] E →L[ℂ] ℂ) (P : PerfectMatching (Fin k ⊕ Fin l))
    (hcross : IsCrossPairing P.1) (x : Fin k → E) (z : Fin l → E) :
    pairingPolynomial sourceFirstRank B P (Sum.elim x z) =
      ∏ i, B (x i) (z (crossPairingEquiv P.1 P.2.1 hcross i)) := by
  classical
  have hleft (i : Fin k) : sourceFirstRank (k := k) (l := l) (Sum.inl i) <
      sourceFirstRank (P.1 (Sum.inl i)) := by
    rw [crossPairingEquiv_left P hcross]
    simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr]
    omega
  have hright (j : Fin l) : ¬ sourceFirstRank (k := k) (l := l) (Sum.inr j) <
      sourceFirstRank (P.1 (Sum.inr j)) := by
    rw [crossPairingEquiv_right P hcross]
    simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr]
    omega
  unfold pairingPolynomial
  rw [Finset.prod_filter, Fintype.prod_sum_type]
  simp only [hleft, hright, ite_true, ite_false, Finset.prod_const_one, mul_one]
  simp only [crossPairingEquiv_left P hcross, Sum.elim_inl, Sum.elim_inr]

/-- The remaining contraction is the matrix coefficient of a position permutation. -/
theorem pairingPolynomial_eq_permutation_coefficient {n : ℕ}
    (J : E → E) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (P : PerfectMatching (Fin n ⊕ Fin n)) (hcross : IsCrossPairing P.1)
    (x y : Fin n → E) :
    pairingPolynomial sourceFirstRank B P (Sum.elim x (J ∘ y)) =
      inner ℂ (completedTensorWord y)
        (completedTensorPermutation (crossPairingEquiv P.1 P.2.1 hcross)
          (completedTensorWord x)) := by
  rw [pairingPolynomial_cross B P hcross, completedTensorPermutation_word,
    inner_completedTensorWord]
  simp only [Function.comp_apply, hB]
  let σ := crossPairingEquiv P.1 P.2.1 hcross
  have heq := Equiv.prod_comp σ (fun j => inner ℂ (y j) (x (σ.symm j)))
  simpa only [Equiv.symm_apply_apply] using heq

/-- Density and boundedness eliminate all same-side terms in the finite-stage
formula and identify the completed operator as a finite sum of permutations. -/
theorem tensorOperator_eq_crossPairingOperator_of_stages {n : ℕ}
    (Y : CompletedTensorWord E n →L[ℂ] CompletedTensorWord E n)
    (J : E → E) (hJ : Continuous J) (hJJ : Function.Involutive J)
    (B : E →L[ℂ] E →L[ℂ] ℂ) (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ)
    (h : ℕ → E) (hh : Orthonormal ℂ h) (hfix : ∀ m, J (h m) = h m)
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ m, S m))
    (hstage : ∀ m, ∀ v : Fin n ⊕ Fin n → E, (∀ i, v i ∈ S m) →
      tracialWordCoefficient Y J v =
        ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    Y = crossPairingOperator c := by
  classical
  have hfull := tracial_pairing_identity_of_stages Y J hJ B sourceFirstRank c
    S hmono hdense hstage
  have hlabels (a b : ℕ) : B (h a) (h b) = if a = b then 1 else 0 := by
    rw [← hfix b, hB]
    simpa only [eq_comm] using (orthonormal_iff_ite.mp hh b a)
  have hexp := labelPairingExpansion_of_tracial_identity Y J B sourceFirstRank
    sourceFirstRank_injective c h hfix hlabels hfull
  have hzero (P : PerfectMatching (Fin n ⊕ Fin n)) (hP : ¬ IsCrossPairing P.1) : c P = 0 := by
    by_contra hc
    exact hP (nonzero_pairing_coefficient_isCrossPairing Y h hh c hexp P hc)
  apply sub_eq_zero.mp
  apply tensorOperator_eq_zero_of_word_coefficients
  intro x y
  have heq := hfull (Sum.elim x (J ∘ y))
  have hsum : (∑ P, c P * pairingPolynomial sourceFirstRank B P (Sum.elim x (J ∘ y))) =
      ∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1},
        c P.1 * pairingPolynomial sourceFirstRank B P.1 (Sum.elim x (J ∘ y)) := by
    symm
    rw [← Finset.sum_subtype
      (p := fun P : PerfectMatching (Fin n ⊕ Fin n) => IsCrossPairing P.1)
      (Finset.univ.filter (fun P : PerfectMatching (Fin n ⊕ Fin n) => IsCrossPairing P.1))
      (by simp) (fun P => c P * pairingPolynomial sourceFirstRank B P (Sum.elim x (J ∘ y)))]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro P _ hP
    have hn : ¬ IsCrossPairing P.1 := by simpa only [Finset.mem_filter,
      Finset.mem_univ, true_and] using hP
    rw [hzero P hn, zero_mul]
  rw [hsum] at heq
  have hJJ' (z : E) : J (J z) = z := hJJ z
  simp only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    hJJ'] at heq
  change inner ℂ (completedTensorWord y)
    (Y (completedTensorWord x) - crossPairingOperator c (completedTensorWord x)) = 0
  rw [inner_sub_right, heq]
  apply sub_eq_zero.mpr
  simp only [crossPairingOperator, sum_apply,
    smul_apply, inner_sum, inner_smul_right,
    LinearIsometry.coe_toContinuousLinearMap]
  apply Finset.sum_congr rfl
  intro P _
  rw [pairingPolynomial_eq_permutation_coefficient J B hB P.1 P.2]

/-- Repeated-letter words see only the sum of the surviving coefficients. -/
theorem crossPairingOperator_constant {n : ℕ}
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ) (x : E) :
    crossPairingOperator c (completedTensorWord (fun _ : Fin n => x)) =
      (∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1}, c P.1) •
        completedTensorWord (fun _ : Fin n => x) := by
  classical
  simp only [crossPairingOperator, sum_apply,
    smul_apply, LinearIsometry.coe_toContinuousLinearMap,
    completedTensorPermutation_constant, Finset.sum_smul]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointTensors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.MatrixHilbertStage.form_apply _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensorInsert_apply _root_.OAI.KadisonSimilarity.hilbertTensorLift_insert _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.hilbertTensorRightInsert_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensorInsert _root_.OAI.KadisonSimilarity.invariantStageForm_apply _root_.OAI.KadisonSimilarity.multiplicitySlice_zero _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_hilbertTensorInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tensorSlice_insert _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed tensor words with an unrestricted first endpoint

The endpoint and the centered tail may live in different Hilbert spaces.
Their completed tensor product has total elementary words and carries
the operators `I ⊗ A` and endpoint slices.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Vanishing matrix coefficients on all endpoint words force the operator to vanish. -/
theorem endpointOperator_eq_zero_of_word_coefficients {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hword : ∀ d x c z, inner ℂ (endpointWord c z) (Y (endpointWord d x)) = 0) : Y = 0 := by
  apply continuousLinearMap_ext_endpointWords
  intro d x
  have hlin : innerSL ℂ (Y (endpointWord d x)) = 0 := by
    apply continuousLinearMap_ext_endpointWords
    intro c z
    change inner ℂ (Y (endpointWord d x)) (endpointWord c z) = 0
    simpa only [inner_conj_symm, map_zero] using
      congrArg (starRingEnd ℂ) (hword d x c z)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have heq := congrArg (fun g : EndpointTensor E F l →L[ℂ] ℂ =>
    g (Y (endpointWord d x))) hlin
  change inner ℂ (Y (endpointWord d x)) (Y (endpointWord d x)) = 0 at heq
  exact heq

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Contracting the endpoint is adjoint to inserting that endpoint. -/
theorem inner_tensorSlice_endpointInsert {n : ℕ} (d : E)
    (x : CompletedTensorWord F n) (z : EndpointTensor E F n) :
    inner ℂ x (tensorSlice d z) = inner ℂ (endpointInsert d x) z := by
  unfold EndpointTensor HilbertTensor at *
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul a b =>
      change inner ℂ x (tensorSlice d (endpointInsert a b)) =
        inner ℂ (endpointInsert d x) (endpointInsert a b)
      have hs : tensorSlice d (endpointInsert a b) = inner ℂ d a • b :=
        (tensorSlice_coe d (a ⊗ₜ[ℂ] b)).trans (algebraTensorSlice_tmul d a b)
      rw [hs, inner_smul_right, inner_endpointInsert]
    | add a b ha hb =>
      change inner ℂ x (tensorSlice d ((a + b : E ⊗[ℂ] CompletedTensorWord F n) :
          HilbertTensor E (CompletedTensorWord F n))) =
        inner ℂ (endpointInsert d x) ((a + b : E ⊗[ℂ] CompletedTensorWord F n) :
          HilbertTensor E (CompletedTensorWord F n))
      have hs : tensorSlice d ((a + b : E ⊗[ℂ] CompletedTensorWord F n) :
          HilbertTensor E (CompletedTensorWord F n)) =
          tensorSlice d (a : HilbertTensor E (CompletedTensorWord F n)) +
            tensorSlice d (b : HilbertTensor E (CompletedTensorWord F n)) :=
        (congrArg (tensorSlice d) (hilbertTensor_coe_add a b)).trans
          ((tensorSlice d).map_add _ _)
      calc
        _ = inner ℂ x (tensorSlice d (a : HilbertTensor E (CompletedTensorWord F n)) +
              tensorSlice d (b : HilbertTensor E (CompletedTensorWord F n))) :=
          congrArg (fun y => inner ℂ x y) hs
        _ = inner ℂ x (tensorSlice d (a : HilbertTensor E (CompletedTensorWord F n))) +
              inner ℂ x (tensorSlice d (b : HilbertTensor E (CompletedTensorWord F n))) :=
          inner_add_right _ _ _
        _ = inner ℂ (endpointInsert d x) (a : HilbertTensor E (CompletedTensorWord F n)) +
              inner ℂ (endpointInsert d x) (b : HilbertTensor E (CompletedTensorWord F n)) :=
          congrArg₂ (· + ·) ha hb
        _ = _ := (congrArg (fun y => inner ℂ (endpointInsert d x) y)
            (hilbertTensor_coe_add a b)).trans (inner_add_right _ _ _) |>.symm

@[simp] theorem endpointCompression_coefficient {k l : ℕ} (Ω : E)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (x : Fin k → F) (z : Fin l → F) :
    inner ℂ (completedTensorWord z) (endpointCompression Ω Y (completedTensorWord x)) =
      inner ℂ (endpointWord Ω z) (Y (endpointWord Ω x)) := by
  simp only [endpointCompression, ContinuousLinearMap.comp_apply,
    inner_tensorSlice_endpointInsert, endpointWord]

/-- Coefficient factorization reconstructs `I_E ⊗ A` using proved totality. -/
theorem endpointOperator_eq_amplification {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l)
    (hcoeff : ∀ d x c z, inner ℂ (endpointWord c z) (Y (endpointWord d x)) =
      inner ℂ c d * inner ℂ (completedTensorWord z) (A (completedTensorWord x))) :
    Y = endpointAmplification A := by
  apply sub_eq_zero.mp
  apply endpointOperator_eq_zero_of_word_coefficients
  intro d x c z
  change inner ℂ (endpointWord c z)
    (Y (endpointWord d x) - endpointAmplification A (endpointWord d x)) = 0
  rw [inner_sub_right, hcoeff]
  simp only [endpointWord, endpointAmplification_insert, inner_endpointInsert, sub_self]

variable [CompleteSpace E]

/-- Moving an endpoint action across an inner product requires only the
ordinary Hilbert adjoint law. -/
theorem inner_endpointHeadAction {n : ℕ} (p : E →L[ℂ] E)
    (c : E) (z : CompletedTensorWord F n) (w : EndpointTensor E F n) :
    inner ℂ (endpointInsert c z) (endpointHeadAction p w) =
      inner ℂ (endpointInsert (p.adjoint c) z) w := by
  have heq := continuousLinearMap_ext_endpointWords
    ((innerSL ℂ (endpointInsert c z)).comp (endpointHeadAction p))
    (innerSL ℂ (endpointInsert (p.adjoint c) z)) (fun d x => by
      change inner ℂ (endpointInsert c z)
        (endpointHeadAction p (endpointInsert d (completedTensorWord x))) =
          inner ℂ (endpointInsert (p.adjoint c) z) (endpointInsert d (completedTensorWord x))
      rw [endpointHeadAction_insert, inner_endpointInsert, inner_endpointInsert,
        p.adjoint_inner_left])
  exact congrArg (fun L : EndpointTensor E F n →L[ℂ] ℂ => L w) heq

/-- Left intertwining moves arbitrary first endpoints to the trace-vector
coefficient. This is the algebraic replacement for a separate commutant theorem. -/
theorem endpoint_coefficient_transfer {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (p : E →L[ℂ] E)
    (hY : Y.comp (endpointHeadAction (n := k) p) =
      (endpointHeadAction (n := l) p).comp Y)
    (Ω c : E) (x : Fin k → F) (z : Fin l → F) :
    inner ℂ (endpointWord c z) (Y (endpointWord (p Ω) x)) =
      inner ℂ (endpointWord (p.adjoint c) z) (Y (endpointWord Ω x)) := by
  have heq := congrArg (fun L : EndpointTensor E F k →L[ℂ] EndpointTensor E F l =>
    L (endpointWord Ω x)) hY
  simp only [ContinuousLinearMap.comp_apply, endpointWord, endpointHeadAction_insert] at heq
  change inner ℂ (endpointInsert c (completedTensorWord z))
    (Y (endpointInsert (p Ω) (completedTensorWord x))) = _
  rw [heq, inner_endpointHeadAction]
  rfl

omit [CompleteSpace E] in
/-- An endpoint and `n` matrix-unit tail letters contribute `n + 1` normalized
Hilbert--Schmidt factors, even when endpoint and tail spaces differ. -/
theorem norm_endpointWord_le_matrix_units {n : ℕ} (d : E) (x : Fin n → F)
    (m : ℝ) (hm : 0 < m) (hd : ‖d‖ ≤ m ^ (-(1 : ℝ) / 2))
    (hx : ∀ i, ‖x i‖ ≤ m ^ (-(1 : ℝ) / 2)) :
    ‖endpointWord d x‖ ≤ m ^ (-((n : ℝ) + 1) / 2) := by
  rw [endpointWord, norm_endpointInsert]
  calc
    _ ≤ m ^ (-(1 : ℝ) / 2) * m ^ (-(n : ℝ) / 2) :=
      mul_le_mul hd (norm_completedTensorWord_le_matrix_units x m hm hx)
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hm]
      congr 1
      ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Density for unrestricted endpoints and centered tensor letters

The two endpoint variables and the finitely many centered letters have different
ambient Hilbert spaces. Nested dense matrix stages nevertheless give a common
stage, so their continuous coefficient identities extend together.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct
universe u

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Continuity of the completed word, including its unrestricted endpoint. -/
theorem continuous_endpointWord (n : ℕ) :
    Continuous (fun p : E × (Fin n → F) => endpointWord p.1 p.2) := by
  have ht : Continuous (fun p : E × (Fin n → F) =>
      p.1 ⊗ₜ[ℂ] completedTensorWord p.2) :=
    TensorProduct.continuous_tmul.comp
      (continuous_fst.prodMk ((continuous_completedTensorWord n).comp continuous_snd))
  exact (UniformSpace.Completion.continuous_coe
    (α := E ⊗[ℂ] CompletedTensorWord F n)).comp ht

omit [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] in
/-- Two groups of finite coordinates can use different Hilbert spaces. -/
theorem continuous_eq_of_two_nested_stages {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : ℕ → Set E) (T : ℕ → Set F) (hS : Monotone S) (hT : Monotone T)
    (hdS : Dense (⋃ n, S n)) (hdT : Dense (⋃ n, T n))
    (f g : (ι → E) × (κ → F) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hstage : ∀ n p, (∀ i, p.1 i ∈ S n) → (∀ j, p.2 j ∈ T n) → f p = g p) :
    f = g := by
  let U : Set E := ⋃ n, S n
  let V : Set F := ⋃ n, T n
  have hs : DenseRange (Pi.map (fun _ : ι => ((↑) : U → E))) :=
    DenseRange.piMap (fun _ => hdS.denseRange_val)
  have ht : DenseRange (Pi.map (fun _ : κ => ((↑) : V → F))) :=
    DenseRange.piMap (fun _ => hdT.denseRange_val)
  apply (hs.prodMap ht).equalizer hf hg
  funext p
  obtain ⟨m, hm⟩ := exists_common_stage S hS (fun i => (p.1 i : E))
    (fun i => (p.1 i).property)
  obtain ⟨n, hn⟩ := exists_common_stage T hT (fun i => (p.2 i : F))
    (fun i => (p.2 i).property)
  exact hstage (max m n) _ (fun i => hS (Nat.le_max_left m n) (hm i))
    (fun j => hT (Nat.le_max_right m n) (hn j))

theorem continuous_endpointTracialCoefficient {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (J : F → F) (hJ : Continuous J) : Continuous (endpointTracialCoefficient Y J) := by
  unfold endpointTracialCoefficient
  have htest : Continuous (fun v : EndpointLetters E F k l =>
      (v.1 true, fun j : Fin l => J (v.2 (Sum.inr j)))) :=
    ((continuous_apply true).comp continuous_fst).prodMk
      (continuous_pi (fun j => hJ.comp ((continuous_apply (Sum.inr j)).comp continuous_snd)))
  have hsource : Continuous (fun v : EndpointLetters E F k l =>
      (v.1 false, fun i : Fin k => v.2 (Sum.inl i))) :=
    ((continuous_apply false).comp continuous_fst).prodMk
      (continuous_pi (fun i => (continuous_apply (Sum.inl i)).comp continuous_snd))
  have htw := (continuous_endpointWord (E := E) (F := F) l).comp htest
  have hsw := (continuous_endpointWord (E := E) (F := F) k).comp hsource
  have hyw := Y.continuous.comp hsw
  simpa only [Function.comp_def] using htw.inner hyw

/-- Extend a stage endpoint pairing formula to all endpoints and tail letters. -/
theorem endpoint_pairing_identity_of_stages {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (J : F → F) (hJ : Continuous J) (B : F →L[ℂ] F →L[ℂ] ℂ)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (S : ℕ → Set E) (T : ℕ → Set F) (hS : Monotone S) (hT : Monotone T)
    (hdS : Dense (⋃ n, S n)) (hdT : Dense (⋃ n, T n))
    (hstage : ∀ n d a v, d ∈ S n → a ∈ S n → (∀ i, v i ∈ T n) →
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v := by
  classical
  let rhs (v : EndpointLetters E F k l) := inner ℂ (v.1 true) (v.1 false) *
    ∑ P, c P * pairingPolynomial sourceFirstRank B P v.2
  have hinner : Continuous (fun v : EndpointLetters E F k l =>
      inner ℂ (v.1 true) (v.1 false)) :=
    ((continuous_apply true).comp continuous_fst).inner ((continuous_apply false).comp continuous_fst)
  have htail : Continuous (fun v : EndpointLetters E F k l =>
      v.2) :=
    continuous_snd
  have hsum : Continuous (fun v : EndpointLetters E F k l =>
      ∑ P, c P * pairingPolynomial sourceFirstRank B P v.2) :=
    continuous_finsetSum _ (fun P _ => continuous_const.mul
      ((continuous_pairingPolynomial sourceFirstRank B P).comp htail))
  have hrhs : Continuous rhs := hinner.mul hsum
  have heq := continuous_eq_of_two_nested_stages S T hS hT hdS hdT
    (endpointTracialCoefficient Y J) rhs (continuous_endpointTracialCoefficient Y J hJ) hrhs
    (fun n v hv hw => hstage n (v.1 false) (v.1 true) v.2 (hv false) (hv true) hw)
  intro d a v
  exact congrFun heq (fun b => if b then a else d, v)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointPairings
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.crossPairingEquiv_left _root_.OAI.KadisonSimilarity.crossPairingEquiv_right _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorization of matrix contractions along pairs

This is the finite combinatorial bridge between the cycle expansion and the
bilinear pairing polynomials: each two-cycle contributes exactly one trace of
a product. The normalization uses the actual number of matching orbits.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The unnormalized coordinate contraction of a matching is a product of
ordinary matrix traces, one for each pair. -/
theorem permutationContraction_matching (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (v : ι → Matrix α α ℂ) :
    permutationContraction P.1 v =
      ∏ i : MatchingRepresentatives rank P, Matrix.trace (v i * v (P.1 i)) := by
  classical
  let R := MatchingRepresentatives rank P
  let e := matchingSplitEquiv rank hrank P
  let d : (ι → α) ≃ (R → α) × (R → α) :=
    (Equiv.arrowCongr e.symm (Equiv.refl α)).trans (Equiv.sumArrowEquivProdArrow R R α)
  unfold permutationContraction
  rw [Fintype.sum_equiv d _ (fun fg =>
    ∏ i : R, v i (fg.1 i) (fg.2 i) * v (P.1 i) (fg.2 i) (fg.1 i))]
  · rw [Fintype.sum_prod_type]
    have hinner (f : R → α) :
        (∑ g : R → α, ∏ i : R, v i.val (f i) (g i) * v (P.1 i.val) (g i) (f i)) =
          ∏ i : R, ∑ b : α, v i.val (f i) b * v (P.1 i.val) b (f i) :=
      (Fintype.prod_sum (fun (i : R) (b : α) =>
        v i.val (f i) b * v (P.1 i.val) b (f i))).symm
    simp_rw [hinner]
    rw [← Fintype.prod_sum (fun (i : R) (a : α) =>
      ∑ b : α, v i.val a b * v (P.1 i.val) b a)]
    apply Finset.prod_congr rfl
    intro i _
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  · intro f
    change (∏ i, v i (f i) (f (P.1 i))) =
      ∏ i : R, v i (f i) (f (P.1 i)) * v (P.1 i) (f (P.1 i)) (f i)
    rw [← e.prod_comp (fun i => v i (f i) (f (P.1 i))), Fintype.prod_sum_type]
    simp only [e, matchingSplitEquiv_inl, matchingSplitEquiv_inr]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [P.2.1]

theorem permutationCycleCount_endpointMatching (rank : ι → ℕ)
    (hrank : Function.Injective rank) (P : PerfectMatching ι) :
    permutationCycleCount (endpointMatching P) =
      Fintype.card (MatchingRepresentatives rank P) + 1 := by
  rw [permutationCycleCount, Nat.card_eq_fintype_card,
    ← Fintype.card_congr (endpointMatchingClassEquiv rank hrank P), Fintype.card_option]

/-- Splitting the endpoint coordinate leaves precisely the tail contraction. -/
theorem permutationContraction_endpointMatching (P : PerfectMatching ι)
    (v : Option ι → Matrix α α ℂ) :
    permutationContraction (endpointMatching P) v =
      Matrix.trace (v none) * permutationContraction P.1 (fun i => v (some i)) := by
  classical
  unfold permutationContraction
  rw [Fintype.sum_equiv (Equiv.piOptionEquivProd (β := fun _ : Option ι => α)) _
    (fun fg => v none fg.1 fg.1 * ∏ i, v (some i) (fg.2 i) (fg.2 (P.1 i)))]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    rfl
  · intro f
    rw [Fintype.prod_option]
    rfl

/-- Each surviving finite-stage cycle form is the endpoint trace times the
product of normalized pair traces. -/
theorem normalizedPermutationContraction_endpointMatching
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (v : Option ι → Matrix α α ℂ) :
    normalizedPermutationContraction (endpointMatching P) v =
      ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        ∏ i : MatchingRepresentatives rank P,
          (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i))) := by
  rw [normalizedPermutationContraction, permutationCycleCount_endpointMatching rank hrank P,
    pow_succ, permutationContraction_endpointMatching,
    permutationContraction_matching rank hrank P, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

/-- Combining the cycle threshold, centered singleton deletion, and explicit
matrix factorization yields exactly the finite-stage pairing expansion. -/
theorem invariant_expansion_tail_pairings
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (v : Option ι → Matrix α α ℂ) (hcenter : ∀ i, Matrix.trace (v (some i)) = 0)
    (c : Equiv.Perm (Option ι) → ℂ)
    (hsmall : ∀ π, 2 * permutationCycleCount π < Fintype.card (Option ι) + 1 → c π = 0) :
    (∑ π, c π * normalizedPermutationContraction π v) =
      ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        ∑ P : PerfectMatching ι, c (endpointMatching P) *
          ∏ i : MatchingRepresentatives rank P,
            (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i))) := by
  classical
  rw [invariant_expansion_reduce_to_pairings none v (by
    intro i hi
    cases i with
    | none => exact False.elim (hi rfl)
    | some i => exact hcenter i) c hsmall]
  rw [Finset.sum_subtype (p := fun π : Equiv.Perm (Option ι) => EndpointPairing π none)
    (Finset.univ.filter (fun π => EndpointPairing π none)) (by simp)
    (fun π => c π * normalizedPermutationContraction π v)]
  rw [← endpointMatchingEquiv.sum_comp]
  simp only [endpointMatchingEquiv_apply,
    normalizedPermutationContraction_endpointMatching rank hrank]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_StableMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stable coefficients on growing matrix stages

Finite Schur--Weyl spanning, compatibility of normalized contractions, and the
actual matrix-unit endpoint estimate produce one stable coefficient family.
The small-cycle coefficients are proved zero; neither stability nor those
zeros are added as assumptions.
-/

noncomputable section
namespace KadisonSimilarity

open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Coefficients chosen by finite Schur--Weyl spanning agree at every stage
once their normalized contractions restrict to the common initial stage. -/
theorem exists_stable_matrix_expansion
    (spanning : ∀ s, SchurWeylMultilinearSpanning ι (A s))
    (F : ∀ s, MultilinearMap ℂ (fun _ : ι => Matrix (A s) (A s) ℂ) ℂ)
    (hF : ∀ s, UnitaryConjugationInvariant (F s))
    (embed : ∀ s, Matrix (A 0) (A 0) ℂ → Matrix (A s) (A s) ℂ)
    (hform : ∀ s v, F s (fun i => embed s (v i)) = F 0 v)
    (hcontraction : ∀ s (π : Equiv.Perm ι) (v : ι → Matrix (A 0) (A 0) ℂ),
      normalizedPermutationContraction π (fun i => embed s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ι → A 0) (hlabels : Function.Injective labels) :
    ∃ c : Equiv.Perm ι → ℂ, ∀ s v,
      F s v = ∑ π, c π * normalizedPermutationContraction π v := by
  choose coeff hcoeff using fun s => spanning s (F s) (hF s)
  have hstable (s : ℕ) : coeff s = coeff 0 := by
    apply normalizedPermutationContraction_coefficients_unique labels hlabels
    intro v
    calc
      (∑ π, coeff s π * normalizedPermutationContraction π v) =
          ∑ π, coeff s π * normalizedPermutationContraction π (fun i => embed s (v i)) := by
        simp only [hcontraction]
      _ = F s (fun i => embed s (v i)) := (hcoeff s _).symm
      _ = F 0 v := hform s v
      _ = ∑ π, coeff 0 π * normalizedPermutationContraction π v := hcoeff 0 v
  refine ⟨coeff 0, fun s v => ?_⟩
  simpa only [hstable s] using hcoeff s v

/-- The endpoint test eliminates every stable coefficient below the cycle
threshold. The input bound is on the original stage form at explicit matrix
units, not on already-isolated coefficients. -/
theorem stable_matrix_coefficient_zero
    (F : ∀ s, MultilinearMap ℂ (fun _ : ι => Matrix (A s) (A s) ℂ) ℂ)
    (c : Equiv.Perm ι → ℂ)
    (hexp : ∀ s v, F s v = ∑ π, c π * normalizedPermutationContraction π v)
    (labels : ∀ s, ι → A s) (hlabels : ∀ s, Function.Injective (labels s))
    (hsize : Tendsto (fun s => (Fintype.card (A s) : ℝ)) atTop atTop)
    (tailDegree : ℕ) (C : ℝ)
    (hbound : ∀ s π, ‖F s (permutationTest (labels s) π)‖ ≤
      C * (Fintype.card (A s) : ℝ) ^ (-1 - (tailDegree : ℝ) / 2))
    (π : Equiv.Perm ι)
    (hfew : (permutationCycleCount π : ℝ) < 1 + (tailDegree : ℝ) / 2) : c π = 0 := by
  apply cycle_coefficient_zero (fun s => (Fintype.card (A s) : ℝ))
    (fun s => by exact_mod_cast Fintype.card_pos (α := A s)) hsize
    tailDegree 0 (permutationCycleCount π) (c π) C (by simpa using hfew)
  intro s
  have hb := hbound s π
  rw [hexp s (permutationTest (labels s) π),
    norm_normalizedPermutationContraction_sum_test (labels s) (hlabels s)] at hb
  simpa using hb

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Assemble finite Schur--Weyl spanning, coefficient stability, endpoint
matrix-unit estimates, and the proved pair-trace factorization. -/
theorem exists_stable_tail_pairing_expansion
    (rank : T → ℕ) (hrank : Function.Injective rank)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option T) (A s))
    (F : ∀ s, MultilinearMap ℂ (fun _ : Option T => Matrix (A s) (A s) ℂ) ℂ)
    (hF : ∀ s, UnitaryConjugationInvariant (F s))
    (embed : ∀ s, Matrix (A 0) (A 0) ℂ → Matrix (A s) (A s) ℂ)
    (hform : ∀ s v, F s (fun i => embed s (v i)) = F 0 v)
    (hcontraction : ∀ s (π : Equiv.Perm (Option T))
      (v : Option T → Matrix (A 0) (A 0) ℂ),
      normalizedPermutationContraction π (fun i => embed s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option T → A s) (hlabels : ∀ s, Function.Injective (labels s))
    (hsize : Tendsto (fun s => (Fintype.card (A s) : ℝ)) atTop atTop)
    (C : ℝ)
    (hbound : ∀ s π, ‖F s (permutationTest (labels s) π)‖ ≤
      C * (Fintype.card (A s) : ℝ) ^ (-1 - (Fintype.card T : ℝ) / 2)) :
    ∃ c : Equiv.Perm (Option T) → ℂ,
      (∀ s v, F s v = ∑ π, c π * normalizedPermutationContraction π v) ∧
      (∀ π, 2 * permutationCycleCount π < Fintype.card (Option T) + 1 → c π = 0) ∧
      (∀ s v, (∀ i : T, Matrix.trace (v (some i)) = 0) →
        F s v = ((Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v none)) *
          ∑ P : PerfectMatching T, c (endpointMatching P) *
            ∏ i : MatchingRepresentatives rank P,
              (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i)))) := by
  obtain ⟨c, hc⟩ := exists_stable_matrix_expansion spanning F hF embed hform hcontraction
    (labels 0) (hlabels 0)
  have hzero (π : Equiv.Perm (Option T))
      (hπ : 2 * permutationCycleCount π < Fintype.card (Option T) + 1) : c π = 0 := by
    apply stable_matrix_coefficient_zero F c hc labels hlabels hsize (Fintype.card T) C hbound π
    have hn : 2 * permutationCycleCount π < Fintype.card T + 2 := by
      simpa only [Fintype.card_option, Nat.add_assoc, one_add_one_eq_two] using hπ
    have hr : (2 : ℝ) * permutationCycleCount π < (Fintype.card T : ℝ) + 2 := by
      exact_mod_cast hn
    linarith
  refine ⟨c, hc, hzero, ?_⟩
  intro s v hv
  rw [hc s v]
  exact invariant_expansion_tail_pairings rank hrank v hv c hzero

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantIntertwiners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.embeddedMatrixStage_center _root_.OAI.KadisonSimilarity.embeddedMatrixStage_full _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensorInsert_apply _root_.OAI.KadisonSimilarity.hilbertTensorLift_insert _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.hilbertTensorRightInsert_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensorInsert _root_.OAI.KadisonSimilarity.multiplicitySlice_zero _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_hilbertTensorInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tensorSlice_insert _root_.OAI.KadisonSimilarity.tracialMatrixStage_full _root_.OAI.KadisonSimilarity.tracialMatrixStage_unit _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix realization of the invariant-intertwiner argument

Finite coefficient forms are constructed from explicit Hilbert-space matrix
realizations. Normalized Hilbert--Schmidt inner products supply the matrix-unit
norms, while left matrix actions supply endpoint transfer. The sole invariant
theory input remains finite-dimensional Schur--Weyl spanning.
-/

noncomputable section
namespace KadisonSimilarity

variable {E F α : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype α] [DecidableEq α]

/-- Every realized matrix unit has the normalized Hilbert--Schmidt norm. -/
theorem MatrixHilbertStage.norm_full_matrixUnit [Nonempty α]
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (a b : α) :
    ‖R.full (tensorMatrixUnit a b)‖ = (Fintype.card α : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hs : ‖R.full (tensorMatrixUnit a b)‖ ^ 2 = (Fintype.card α : ℝ)⁻¹ := by
    rw [@norm_sq_eq_re_inner ℂ, R.inner_full, star_tensorMatrixUnit,
      tensorMatrixUnit_mul, trace_tensorMatrixUnit, mul_one]
    simp
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.rpow_nonneg hm.le _)).mp
  rw [hs, ← Real.rpow_mul_natCast hm.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg_one]

/-- Centering is contractive on the normalized matrix units. -/
theorem MatrixHilbertStage.norm_center_matrixUnit_le [Nonempty α]
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (a b : α) :
    ‖R.center (tensorMatrixUnit a b)‖ ≤ (Fintype.card α : ℝ) ^ (-(1 : ℝ) / 2) := by
  simpa only [R.norm_full_matrixUnit] using R.norm_center_le (tensorMatrixUnit a b)

variable {k l : ℕ}

/-- Isometric word covariance gives precisely the finite conjugation invariance
required by Schur--Weyl, with no invariance of the coefficient form assumed. -/
theorem MatrixHilbertStage.form_invariant_of_word_covariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (Wk : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k)
    (Wl : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l)
    (hY : ∀ u, Y.comp (Wk u).toContinuousLinearMap = (Wl u).toContinuousLinearMap.comp Y)
    (hsource : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
      endpointWord Ω (fun i => R.center ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
        Wk u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i))))))
    (htest : ∀ (u : Matrix.unitaryGroup α ℂ) (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
      endpointWord (R.full (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
        (fun j => J (R.center ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
        Wl u (endpointWord (R.full (star (v none)))
          (fun j => J (R.center (v (some (Sum.inr j))))))) :
    UnitaryConjugationInvariant (R.form J Ω Y) := by
  intro u v
  simp only [R.form_apply]
  rw [hsource u v, htest u v]
  have heq := congrArg (fun L : EndpointTensor E F k →L[ℂ] EndpointTensor E F l =>
    L (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))) (hY u)
  change Y (Wk u _) = Wl u (Y _) at heq
  rw [heq, (Wl u).inner_map_map]

/-- The matrix-unit endpoint estimate follows from the actual left matrix
projection and normalized Hilbert--Schmidt norms. -/
theorem MatrixHilbertStage.form_matrixUnit_bound [Nonempty α]
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (hΩ : R.full 1 = Ω)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hY : ∀ a : Matrix α α ℂ, Y.comp (endpointHeadAction (n := k) (R.left a)) =
      (endpointHeadAction (n := l) (R.left a)).comp Y)
    (labels : Option (Fin k ⊕ Fin l) → α) (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) :
    ‖R.form J Ω Y (permutationTest labels π)‖ ≤
      ‖Y‖ * (Fintype.card α : ℝ) ^ (-1 - ((k : ℝ) + l) / 2) := by
  let v := permutationTest labels π
  let b := labels (π none)
  let q := R.left (tensorMatrixUnit b b)
  let a := R.full (star (v none))
  let x : Fin k → F := fun i => R.center (v (some (Sum.inl i)))
  let z : Fin l → F := fun j => J (R.center (v (some (Sum.inr j))))
  have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hqa : q.adjoint a = a := by
    dsimp [q, a, v, permutationTest, b]
    rw [R.left_adjoint, star_tensorMatrixUnit, star_tensorMatrixUnit,
      R.left_apply, tensorMatrixUnit_mul]
  have hqΩ : q Ω = R.full (tensorMatrixUnit b b) := by
    rw [← hΩ]
    exact (R.left_apply _ _).trans (by rw [mul_one])
  have ht := endpoint_coefficient_transfer Y q (hY (tensorMatrixUnit b b)) Ω a x z
  rw [hqa] at ht
  have htest : ‖endpointWord a z‖ ≤
      (Fintype.card α : ℝ) ^ (-((l : ℝ) + 1) / 2) := by
    apply norm_endpointWord_le_matrix_units a z _ hm
    · dsimp [a, v, permutationTest]
      rw [star_tensorMatrixUnit, R.norm_full_matrixUnit]
    · intro j
      change ‖J (R.center (tensorMatrixUnit _ _))‖ ≤ _
      rw [J.norm_map]
      exact R.norm_center_matrixUnit_le _ _
  have hsource : ‖endpointWord (q Ω) x‖ ≤
      (Fintype.card α : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
    apply norm_endpointWord_le_matrix_units (q Ω) x _ hm
    · rw [hqΩ, R.norm_full_matrixUnit]
    · intro i
      exact R.norm_center_matrixUnit_le _ _
  change ‖inner ℂ (endpointWord a z) (Y (endpointWord Ω x))‖ ≤ _
  rw [← ht]
  calc
    _ ≤ ‖endpointWord a z‖ * ‖Y (endpointWord (q Ω) x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖endpointWord a z‖ * (‖Y‖ * ‖endpointWord (q Ω) x‖) :=
      mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _)
    _ = ‖Y‖ * (‖endpointWord a z‖ * ‖endpointWord (q Ω) x‖) := by ring
    _ ≤ ‖Y‖ * ((Fintype.card α : ℝ) ^ (-((l : ℝ) + 1) / 2) *
        (Fintype.card α : ℝ) ^ (-((k : ℝ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul htest hsource (norm_nonneg _) (by positivity))
        (norm_nonneg Y)
    _ = _ := by rw [← Real.rpow_add hm]; congr 2; ring

theorem MatrixWordCovariance.form_invariant
    {R : MatrixHilbertStage (E := E) (F := F) (α := α)} {J : F →ₗᵢ⋆[ℂ] F}
    {Ω : E} {Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l}
    (cov : MatrixWordCovariance R J Ω Y) : UnitaryConjugationInvariant (R.form J Ω Y) :=
  R.form_invariant_of_word_covariance J Ω Y cov.sourceAction cov.testAction
    cov.intertwine cov.source_covariance cov.test_covariance

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The coefficient forms agree under an inclusion agreeing on the full and
centered Hilbert realizations. Star compatibility is supplied by the actual
matrix star-algebra inclusion. -/
theorem MatrixHilbertStage.form_compatible
    (R : MatrixHilbertStage (E := E) (F := F) (α := α))
    (S : MatrixHilbertStage (E := E) (F := F) (α := β))
    (J : F →ₗᵢ⋆[ℂ] F) (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (e : Matrix α α ℂ →⋆ₐ[ℂ] Matrix β β ℂ)
    (hfull : ∀ a, S.full (e a) = R.full a)
    (hcenter : ∀ a, S.center (e a) = R.center a)
    (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ) :
    S.form J Ω Y (fun i => e (v i)) = R.form J Ω Y v := by
  simp only [MatrixHilbertStage.form_apply, ← map_star, hfull, hcenter]

/-- Moving a general source endpoint across the intertwiner turns the endpoint
trace into the full Hilbert inner product. The centered matrix pairing is the
ordinary normalized trace pairing on this local stage. -/
theorem MatrixHilbertStage.endpoint_pairing_of_form
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (hΩ : R.full 1 = Ω)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hY : ∀ a, Y.comp (endpointHeadAction (n := k) (R.left a)) =
      (endpointHeadAction (n := l) (R.left a)).comp Y)
    (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hB : ∀ a b, Matrix.trace a = 0 → Matrix.trace b = 0 →
      B (R.center a) (R.center b) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace (a * b))
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hform : ∀ v, (∀ i : Fin k ⊕ Fin l, Matrix.trace (v (some i)) = 0) →
      R.form J Ω Y v = ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        ∑ P, c P * ∏ i : MatchingRepresentatives sourceFirstRank P,
          (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i))))
    (d a : Matrix α α ℂ) (v : Fin k ⊕ Fin l → Matrix α α ℂ)
    (hv : ∀ i, Matrix.trace (v i) = 0) :
    inner ℂ (endpointWord (R.full a) (fun j => J (R.center (v (.inr j)))))
      (Y (endpointWord (R.full d) (fun i => R.center (v (.inl i))))) =
    inner ℂ (R.full a) (R.full d) *
      ∑ P, c P * pairingPolynomial sourceFirstRank B P (fun i => R.center (v i)) := by
  classical
  let w : Option (Fin k ⊕ Fin l) → Matrix α α ℂ := Option.elim' (star a * d) v
  have hp : R.left d Ω = R.full d := by rw [← hΩ, R.left_apply, mul_one]
  have hpa : (R.left d).adjoint (R.full a) = R.full (star d * a) := by
    rw [R.left_adjoint, R.left_apply]
  have ht := endpoint_coefficient_transfer Y (R.left d) (hY d) Ω (R.full a)
    (fun i => R.center (v (.inl i))) (fun j => J (R.center (v (.inr j))))
  rw [hp, hpa] at ht
  have hw : R.form J Ω Y w =
      inner ℂ (endpointWord (R.full (star d * a)) (fun j => J (R.center (v (.inr j)))))
        (Y (endpointWord Ω (fun i => R.center (v (.inl i))))) := by
    simp only [R.form_apply, w, Option.elim'_none, Option.elim'_some, star_mul,
      star_star]
  rw [ht, ← hw, hform w (fun i => hv i), R.inner_full]
  change _ * _ = _ * _
  congr 1
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  unfold pairingPolynomial
  simp only [hB _ _ (hv _) (hv _)]
  symm
  exact Finset.prod_subtype
    (Finset.univ.filter (fun i => sourceFirstRank i < sourceFirstRank (P.1 i)))
    (by simp) (fun i => (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v i * v (P.1 i)))


section GrowingStages

variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Assemble the actual stage forms, their covariance, their left-matrix test
estimate, and the finite invariant theory. The only published assumption is
`spanning`; every other premise is explicit local realization data. -/
theorem exists_realized_matrix_pairing_expansion
    (R : ∀ s, MatrixHilbertStage (E := E) (F := F) (α := A s))
    (J : F →ₗᵢ⋆[ℂ] F) (Ω : E) (hΩ : ∀ s, (R s).full 1 = Ω)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := k) ((R s).left a)) =
      (endpointHeadAction (n := l) ((R s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (R s) J Ω Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (e : ∀ s, Matrix (A 0) (A 0) ℂ →⋆ₐ[ℂ] Matrix (A s) (A s) ℂ)
    (hfull : ∀ s a, (R s).full (e s a) = (R 0).full a)
    (hcenter : ∀ s a, (R s).center (e s a) = (R 0).center a)
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => e s (v i)) = normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s))
    (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop) :
    ∃ c : Equiv.Perm (Option (Fin k ⊕ Fin l)) → ℂ,
      (∀ s v, (R s).form J Ω Y v = ∑ π, c π * normalizedPermutationContraction π v) ∧
      (∀ π, 2 * permutationCycleCount π < Fintype.card (Option (Fin k ⊕ Fin l)) + 1 → c π = 0) ∧
      (∀ s v, (∀ i : Fin k ⊕ Fin l, Matrix.trace (v (some i)) = 0) →
        (R s).form J Ω Y v = ((Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v none)) *
          ∑ P : PerfectMatching (Fin k ⊕ Fin l), c (endpointMatching P) *
            ∏ i : MatchingRepresentatives sourceFirstRank P,
              (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i)))) := by
  apply exists_stable_tail_pairing_expansion sourceFirstRank sourceFirstRank_injective
    spanning (fun s => (R s).form J Ω Y) (fun s => (cov s).form_invariant)
    (fun s => e s) ?_ hcontraction labels hlabels hsize ‖Y‖ ?_
  · intro s v
    exact (R 0).form_compatible (R s) J Ω Y (e s) (hfull s) (hcenter s) v
  · intro s π
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using
      (R s).form_matrixUnit_bound J Ω (hΩ s) Y (hleft s) (labels s) π

end GrowingStages

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_EndpointClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensorInsert_apply _root_.OAI.KadisonSimilarity.hilbertTensorLift_insert _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.hilbertTensorRightInsert_apply _root_.OAI.KadisonSimilarity.inner_hilbertTensorInsert _root_.OAI.KadisonSimilarity.multiplicitySlice_zero _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_hilbertTensorInsert _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tensorSlice_insert _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed invariant intertwiners from matrix-stage geometry

Finite-dimensional Schur--Weyl spanning is the only invariant-theory input.
The remaining assumptions describe a nested dense tracial matrix realization,
its conjugation, and the operator's actual left and conjugation intertwinings.
The coefficient identity and completed permutation classification are derived.
-/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

variable {k l : ℕ}

/-- The full completed coefficient formula is derived from stage geometry,
left intertwining, and finite Schur--Weyl, rather than assumed. -/
theorem exists_endpoint_pairing_expansion_of_schurWeyl
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := k) ((T.stage s).left a)) =
      (endpointHeadAction (n := l) ((T.stage s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) :
    ∃ c : PerfectMatching (Fin k ⊕ Fin l) → ℂ, ∀ d a v,
      inner ℂ (endpointWord a (fun j => T.conjugation (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank T.pairing P v := by
  obtain ⟨coeff, _, _, hforms⟩ := exists_realized_matrix_pairing_expansion T.stage
    T.conjugation T.traceVector T.unit_realization Y hleft cov spanning T.inclusion
    T.full_compatible T.center_compatible hcontraction labels hlabels T.size_tendsto
  refine ⟨fun P => coeff (endpointMatching P), ?_⟩
  apply endpoint_pairing_identity_of_stages Y T.conjugation T.conjugation.continuous T.pairing
    (fun P => coeff (endpointMatching P)) (fullMatrixStage T.stage)
    (centeredMatrixStage T.stage) T.full_mono T.center_mono T.full_dense T.center_dense
  intro s d a v hd ha hv
  obtain ⟨d', rfl⟩ := hd
  obtain ⟨a', rfl⟩ := ha
  choose v' htrace heq using hv
  have hv' : v = fun i => (T.stage s).center (v' i) := funext (fun i => (heq i).symm)
  rw [hv']
  exact (T.stage s).endpoint_pairing_of_form T.conjugation T.traceVector
    (T.unit_realization s) Y (hleft s) T.pairing (T.pairing_matrix s)
    (fun P => coeff (endpointMatching P)) (hforms s) d' a' v' htrace

omit [CompleteSpace E] in
/-- A full endpoint pairing formula reconstructs the identity on the endpoint
factor and the compression to the normalized trace vector. -/
theorem endpoint_reconstruct_from_pairing
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (J : F → F) (hJJ : Function.Involutive J)
    (B : F →L[ℂ] F →L[ℂ] ℂ) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hfull : ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    Y = endpointAmplification (endpointCompression Ω Y) ∧
      (∀ v, tracialWordCoefficient (endpointCompression Ω Y) J v =
        ∑ P, c P * pairingPolynomial sourceFirstRank B P v) := by
  have hunit : inner ℂ Ω Ω = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  have hc : ∀ v, tracialWordCoefficient (endpointCompression Ω Y) J v =
      ∑ P, c P * pairingPolynomial sourceFirstRank B P v := by
    intro v
    rw [tracialWordCoefficient, endpointCompression_coefficient, hfull Ω Ω v, hunit, one_mul]
  refine ⟨?_, hc⟩
  apply endpointOperator_eq_amplification
  intro d x a z
  have hx := hfull d a (Sum.elim x (J ∘ z))
  have hz := hc (Sum.elim x (J ∘ z))
  have hJJ' (y : F) : J (J y) = y := hJJ y
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, hJJ'] at hx
  simp only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, hJJ'] at hz
  rw [hx, hz]

omit [CompleteSpace E] in
/-- Unequal degrees force the full endpoint operator to vanish. -/
theorem endpoint_zero_from_pairing
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (J : F → F) (hJ : Continuous J)
    (hJJ : Function.Involutive J) (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (h : ℕ → F) (hh : Orthonormal ℂ h) (hfix : ∀ m, J (h m) = h m)
    (hfull : ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v)
    (hkl : k ≠ l) : Y = 0 := by
  obtain ⟨hrec, hcoeff⟩ := endpoint_reconstruct_from_pairing Y Ω hΩ J hJJ B c hfull
  have hlabels (a b : ℕ) : B (h a) (h b) = if a = b then 1 else 0 := by
    rw [← hfix b, hB]
    simpa only [eq_comm] using (orthonormal_iff_ite.mp hh b a)
  have hzero := tensorOperator_eq_zero_of_tracial_stages (endpointCompression Ω Y)
    J hJ hJJ B sourceFirstRank sourceFirstRank_injective c h hh hfix hlabels
    (fun _ => Set.univ) (fun _ _ _ => Set.Subset.refl _)
    (by simpa only [Set.iUnion_const] using (dense_univ : Dense (Set.univ : Set F)))
    (fun _ v _ => hcoeff v) hkl
  rw [hrec]
  apply continuousLinearMap_ext_endpointWords
  intro d x
  simp only [endpointWord, endpointAmplification_insert, hzero,
    zero_apply, map_zero]

omit [CompleteSpace E] in
/-- Equal degrees give an actual finite sum of position permutations, with
identity on the unrestricted endpoint. -/
theorem endpoint_permutations_from_pairing {n : ℕ}
    (Y : EndpointTensor E F n →L[ℂ] EndpointTensor E F n)
    (Ω : E) (hΩ : ‖Ω‖ = 1) (J : F → F) (hJ : Continuous J)
    (hJJ : Function.Involutive J) (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ)
    (h : ℕ → F) (hh : Orthonormal ℂ h) (hfix : ∀ m, J (h m) = h m)
    (hfull : ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    Y = endpointAmplification (crossPairingOperator c) := by
  obtain ⟨hrec, hcoeff⟩ := endpoint_reconstruct_from_pairing Y Ω hΩ J hJJ B c hfull
  have hperm := tensorOperator_eq_crossPairingOperator_of_stages (endpointCompression Ω Y)
    J hJ hJJ B hB c h hh hfix (fun _ => Set.univ) (fun _ _ _ => Set.Subset.refl _)
    (by simpa only [Set.iUnion_const] using (dense_univ : Dense (Set.univ : Set F)))
    (fun _ v _ => hcoeff v)
  rwa [hperm] at hrec

/-- The unequal-degree invariant-intertwiner theorem, conditional only on
finite Schur--Weyl and explicit tracial matrix realization data. -/
theorem endpoint_intertwiner_zero_of_schurWeyl
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := k) ((T.stage s).left a)) =
      (endpointHeadAction (n := l) ((T.stage s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (hkl : k ≠ l) : Y = 0 := by
  obtain ⟨c, hc⟩ := exists_endpoint_pairing_expansion_of_schurWeyl
    T Y hleft cov spanning hcontraction labels hlabels
  exact endpoint_zero_from_pairing Y T.traceVector T.norm_traceVector T.conjugation
    T.conjugation.continuous T.conjugation_involutive T.pairing T.pairing_conjugation
    c T.realOrthonormal T.realOrthonormal_orthonormal T.realOrthonormal_fixed hc hkl

/-- The equal-degree invariant-intertwiner theorem on the completed endpoint
Hilbert tensor space; the coefficient expansion is a proved conclusion. -/
theorem endpoint_intertwiner_permutations_of_schurWeyl {n : ℕ}
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : EndpointTensor E F n →L[ℂ] EndpointTensor E F n)
    (hleft : ∀ s a, Y.comp (endpointHeadAction (n := n) ((T.stage s).left a)) =
      (endpointHeadAction (n := n) ((T.stage s).left a)).comp Y)
    (cov : ∀ s, MatrixWordCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin n ⊕ Fin n)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin n ⊕ Fin n))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin n ⊕ Fin n) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) :
    ∃ c : PerfectMatching (Fin n ⊕ Fin n) → ℂ,
      Y = endpointAmplification (crossPairingOperator c) := by
  obtain ⟨c, hc⟩ := exists_endpoint_pairing_expansion_of_schurWeyl
    T Y hleft cov spanning hcontraction labels hlabels
  exact ⟨c, endpoint_permutations_from_pairing Y T.traceVector T.norm_traceVector
    T.conjugation T.conjugation.continuous T.conjugation_involutive T.pairing
    T.pairing_conjugation c T.realOrthonormal T.realOrthonormal_orthonormal
    T.realOrthonormal_fixed hc⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalizedContractions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Naturality of normalized permutation contractions under trace-preserving
matrix algebra maps, proved by deleting one permutation vertex at a time. -/

noncomputable section
namespace KadisonSimilarity

open Finset

universe u
variable {ι : Type u} {α β : Type*} [Fintype ι] [decι : DecidableEq ι]

theorem permutationCycleCount_insert (p : Equiv.Perm ι) (b : ι) :
    permutationCycleCount (insertPermutationVertex p b) = permutationCycleCount p := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  have h := Fintype.card_congr (insertedCycleLabelingsEquiv p b (Fin 2))
  simpa only [card_cycleConstantLabelings, Fintype.card_fin] using h

theorem permutationCycleCount_optionCongr (p : Equiv.Perm ι) :
    permutationCycleCount p.optionCongr = permutationCycleCount p + 1 := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  have h := Fintype.card_congr (fixedCycleLabelingsEquiv p (Fin 2))
  simpa only [card_cycleConstantLabelings, Fintype.card_prod, Fintype.card_fin,
    pow_succ, Nat.mul_comm] using h

variable [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- A fixed vertex contributes the ordinary matrix trace. -/
theorem permutationContraction_optionCongr (p : Equiv.Perm ι)
    (v : Option ι → Matrix α α ℂ) :
    permutationContraction p.optionCongr v =
      Matrix.trace (v none) * permutationContraction p (fun i => v (some i)) := by
  unfold permutationContraction
  rw [Fintype.sum_equiv (Equiv.piOptionEquivProd :
    (Option ι → α) ≃ α × (ι → α)) _
    (fun ag => v none ag.1 ag.1 * ∏ i, v (some i) (ag.2 i) (ag.2 (p i)))]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    rfl
  · intro f
    simp [Fintype.prod_option]

omit [DecidableEq α] in
/-- Summing the label at an inserted nonfixed vertex is matrix multiplication. -/
theorem permutationContraction_insert (p : Equiv.Perm ι) (b : ι)
    (v : Option ι → Matrix α α ℂ) :
    permutationContraction (insertPermutationVertex p b) v =
      permutationContraction p (splicePermutationWord v b) := by
  unfold permutationContraction
  rw [Fintype.sum_equiv (Equiv.piOptionEquivProd :
    (Option ι → α) ≃ α × (ι → α)) _
    (fun ag => v none ag.1 (ag.2 (p b)) *
      (v (some b) (ag.2 b) ag.1 *
        ∏ i : {i : ι // i ≠ b}, v (some i) (ag.2 i) (ag.2 (p i))))]
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    have hreorder (a : α) :
        v none a (g (p b)) * (v (some b) (g b) a *
            ∏ i : {i : ι // i ≠ b}, v (some i) (g i) (g (p i))) =
          (v (some b) (g b) a * v none a (g (p b))) *
            ∏ i : {i : ι // i ≠ b}, v (some i) (g i) (g (p i)) := by ring
    simp_rw [hreorder]
    rw [← Finset.sum_mul]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ b]
    change ((v (some b) * v none) (g b) (g (p b))) * _ = _
    simp only [splicePermutationWord, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp only [Function.update_of_ne i.2]
  · intro f
    rw [Fintype.prod_option, Fintype.prod_eq_mul_prod_subtype_ne _ b]
    simp only [insertPermutationVertex_none, insertPermutationVertex_self,
      Equiv.piOptionEquivProd]
    congr 2
    apply Finset.prod_congr rfl
    intro i _
    rw [insertPermutationVertex_other p b i i.2]
    rfl

omit [DecidableEq α] in
/-- Normalized fixed-point deletion carries precisely one normalized trace. -/
theorem normalizedPermutationContraction_optionCongr (p : Equiv.Perm ι)
    (v : Option ι → Matrix α α ℂ) :
    normalizedPermutationContraction p.optionCongr v =
      ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        normalizedPermutationContraction p (fun i => v (some i)) := by
  rw [normalizedPermutationContraction, permutationCycleCount_optionCongr,
    permutationContraction_optionCongr, normalizedPermutationContraction, pow_succ]
  ring

omit [DecidableEq α] in
/-- Insertion into an existing cycle adds no trace-normalization factor. -/
theorem normalizedPermutationContraction_insert (p : Equiv.Perm ι) (b : ι)
    (v : Option ι → Matrix α α ℂ) :
    normalizedPermutationContraction (insertPermutationVertex p b) v =
      normalizedPermutationContraction p (splicePermutationWord v b) := by
  rw [normalizedPermutationContraction, permutationCycleCount_insert,
    permutationContraction_insert, normalizedPermutationContraction]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem permutationCycleCount_permCongr (e : ι ≃ κ) (p : Equiv.Perm ι) :
    permutationCycleCount (e.permCongr p) = permutationCycleCount p := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  have h := Fintype.card_congr (reindexedCycleLabelingsEquiv e p (Fin 2))
  simpa only [card_cycleConstantLabelings, Fintype.card_fin] using h

omit [DecidableEq α] in
theorem permutationContraction_permCongr (e : ι ≃ κ) (p : Equiv.Perm ι)
    (v : κ → Matrix α α ℂ) :
    permutationContraction (e.permCongr p) v =
      permutationContraction p (fun i => v (e i)) := by
  unfold permutationContraction
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl α))
  intro f
  apply Fintype.prod_equiv e.symm
  intro i
  simp [Equiv.permCongr_apply, Equiv.arrowCongr]

omit [DecidableEq α] in
theorem normalizedPermutationContraction_permCongr (e : ι ≃ κ) (p : Equiv.Perm ι)
    (v : κ → Matrix α α ℂ) :
    normalizedPermutationContraction (e.permCongr p) v =
      normalizedPermutationContraction p (fun i => v (e i)) := by
  rw [normalizedPermutationContraction, permutationCycleCount_permCongr,
    permutationContraction_permCongr, normalizedPermutationContraction]

/-- Normalized permutation contractions are natural for every trace-preserving
unital matrix algebra map; no normal-form hypothesis on that map is needed. -/
theorem normalizedPermutationContraction_map
    [Fintype β] [DecidableEq β]
    (φ : Matrix α α ℂ →ₐ[ℂ] Matrix β β ℂ)
    (htrace : ∀ a, (Fintype.card β : ℂ)⁻¹ * Matrix.trace (φ a) =
      (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    (p : Equiv.Perm ι) (v : ι → Matrix α α ℂ) :
      normalizedPermutationContraction p (fun i => φ (v i)) =
      normalizedPermutationContraction p v := by
  classical
  let Q (I : Type u) [hI : Fintype I] : Prop :=
    ∀ (d : DecidableEq I) (p : Equiv.Perm I) (v : I → Matrix α α ℂ),
      @normalizedPermutationContraction I β hI d _ p (fun i => φ (v i)) =
        @normalizedPermutationContraction I α hI d _ p v
  suffices hQ : Q ι from hQ decι p v
  refine Fintype.induction_empty_option (P := Q) ?_ ?_ ?_ ι
  · intro I J _ e ih
    let : Fintype I := Fintype.ofEquiv J e.symm
    dsimp only [Q] at ih ⊢
    intro d p v
    let : DecidableEq J := d
    let : DecidableEq I := Classical.decEq I
    have hp : e.permCongr (e.symm.permCongr p) = p := e.permCongr.apply_symm_apply p
    have hleft := normalizedPermutationContraction_permCongr e (e.symm.permCongr p)
      (fun i => φ (v i))
    have hright := normalizedPermutationContraction_permCongr e (e.symm.permCongr p) v
    rw [hp] at hleft hright
    exact hleft.trans ((ih (Classical.decEq I) (e.symm.permCongr p)
      (fun i => v (e i))).trans hright.symm)
  · dsimp only [Q]
    intro d p v
    cases Subsingleton.elim d (inferInstance : DecidableEq PEmpty)
    simp [normalizedPermutationContraction, permutationContraction, permutationCycleCount]
  · intro I _ ih
    dsimp only [Q] at ih ⊢
    intro d p v
    let : DecidableEq I := Classical.decEq I
    cases Subsingleton.elim d (@Option.instDecidableEq I (Classical.decEq I))
    obtain ⟨⟨a, q⟩, rfl⟩ := Equiv.Perm.decomposeOption.symm.surjective p
    cases a with
    | none =>
      have hp : Equiv.Perm.decomposeOption.symm (none, q) = q.optionCongr := by
        simp [Equiv.Perm.decomposeOption]
        rfl
      rw [hp]
      rw [normalizedPermutationContraction_optionCongr,
        normalizedPermutationContraction_optionCongr, htrace,
        ih (Classical.decEq I) q (fun i => v (some i))]
    | some a =>
      have hp : Equiv.Perm.decomposeOption.symm (some a, q) =
          insertPermutationVertex q (q.symm a) := by
        simp [Equiv.Perm.decomposeOption, insertPermutationVertex]
      rw [hp]
      rw [normalizedPermutationContraction_insert q (q.symm a) (fun i => φ (v i)),
        normalizedPermutationContraction_insert q (q.symm a) v]
      have hw : splicePermutationWord (fun i => φ (v i)) (q.symm a) =
          fun i => φ (splicePermutationWord v (q.symm a) i) := by
        funext i
        simp only [splicePermutationWord, Function.update_apply]
        split_ifs <;> simp only [map_mul]
      rw [hw]
      exact ih (Classical.decEq I) q (splicePermutationWord v (q.symm a))

section TracialTower

variable {R E : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  {τ : R →ₗ[ℂ] ℂ} {V : R →ₗ[ℂ] E}

/-- The stable-stage contraction compatibility follows from the raw tracial
matrix inclusions and is not an additional tensor-classification hypothesis. -/
theorem NestedTracialMatrices.normalizedPermutationContraction_inclusion
    (M : NestedTracialMatrices (A := A) τ V) (s t : ℕ) (h : s ≤ t)
    (p : Equiv.Perm ι) (v : ι → Matrix (A s) (A s) ℂ) :
    normalizedPermutationContraction p (fun i => M.inclusion s t h (v i)) =
      normalizedPermutationContraction p v := by
  apply normalizedPermutationContraction_map (M.inclusion s t h).toAlgHom ?_ p v
  intro a
  calc
    _ = τ (M.embedding t (M.inclusion s t h a)) := (M.trace_embedding t _).symm
    _ = τ (M.embedding s a) := congrArg τ (M.compatible s t h a)
    _ = _ := M.trace_embedding s a

end TracialTower

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_MultiplicityClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.reducedCreator_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert multiplicities in the invariant-intertwiner theorem

Scalar matrix coefficients in the multiplicity Hilbert space are genuine
bounded endpoint intertwiners. Tensor totality reconstructs the full operator
from these slices. Repeated-letter compressions provide the bounded operator
on the multiplicity space used in propagation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {G H K L : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] in
/-- Inner products with elementary tensors are exactly multiplicity slices. -/
theorem inner_multiplicitySlice (Y : HilbertTensor G H →L[ℂ] HilbertTensor G K)
    (a b : G) (x : H) (z : K) :
    inner ℂ z (multiplicitySlice Y a b x) =
      inner ℂ (hilbertTensorInsert b z) (Y (hilbertTensorInsert a x)) := by
  change inner ℂ z (tensorSlice b (Y (hilbertTensorInsert a x))) = _
  generalize Y (hilbertTensorInsert a x) = w
  induction w using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih w =>
    induction w using OAI.tensorInductionOn with
    | tmul c y =>
      change inner ℂ z (tensorSlice b (hilbertTensorInsert c y)) =
        inner ℂ (hilbertTensorInsert b z) (hilbertTensorInsert c y)
      rw [tensorSlice_insert, inner_smul_right, inner_hilbertTensorInsert]
    | add u v hu hv =>
      have hs : tensorSlice b ((u + v : G ⊗[ℂ] K) : HilbertTensor G K) =
          tensorSlice b (u : HilbertTensor G K) + tensorSlice b (v : HilbertTensor G K) :=
        (congrArg (tensorSlice b) (hilbertTensor_coe_add u v)).trans
          ((tensorSlice b).map_add _ _)
      calc
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor G K) +
              tensorSlice b (v : HilbertTensor G K)) := congrArg (fun y => inner ℂ z y) hs
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor G K)) +
              inner ℂ z (tensorSlice b (v : HilbertTensor G K)) := inner_add_right _ _ _
        _ = inner ℂ (hilbertTensorInsert b z) (u : HilbertTensor G K) +
              inner ℂ (hilbertTensorInsert b z) (v : HilbertTensor G K) := congrArg₂ (· + ·) hu hv
        _ = _ := ((congrArg (fun y => inner ℂ (hilbertTensorInsert b z) y)
            (hilbertTensor_coe_add u v)).trans (inner_add_right _ _ _)).symm

omit [CompleteSpace H] in
theorem norm_hilbertTensorRightInsert_le (w : H) :
    ‖hilbertTensorRightInsert (G := G) w‖ ≤ ‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  rw [hilbertTensorRightInsert_apply, norm_hilbertTensorInsert, mul_comm]

variable [CompleteSpace G]

omit [CompleteSpace H] in
theorem norm_multiplicityCompression_le
    (Y : HilbertTensor G H →L[ℂ] HilbertTensor G H) (w : H) (hw : ‖w‖ = 1) :
    ‖multiplicityCompression Y w‖ ≤ ‖Y‖ := by
  have hi : ‖hilbertTensorRightInsert (G := G) w‖ ≤ 1 := by
    simpa only [hw] using norm_hilbertTensorRightInsert_le (G := G) w
  calc
    _ ≤ ‖(hilbertTensorRightInsert (G := G) w).adjoint‖ *
        (‖Y‖ * ‖hilbertTensorRightInsert (G := G) w‖) :=
      le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖hilbertTensorRightInsert (G := G) w‖ *
        (‖Y‖ * ‖hilbertTensorRightInsert (G := G) w‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * (‖Y‖ * 1) := mul_le_mul hi
      (mul_le_mul_of_nonneg_left hi (norm_nonneg Y)) (by positivity) (by positivity)
    _ = ‖Y‖ := by ring

theorem inner_multiplicityCompression
    (Y : HilbertTensor G H →L[ℂ] HilbertTensor G H) (w : H) (a b : G) :
    inner ℂ b (multiplicityCompression Y w a) =
      inner ℂ w (multiplicitySlice Y a b w) := by
  change inner ℂ b ((hilbertTensorRightInsert w).adjoint
    (Y (hilbertTensorRightInsert w a))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, hilbertTensorRightInsert_apply,
    hilbertTensorRightInsert_apply, inner_multiplicitySlice]

section EndpointMultiplicity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [CompleteSpace E] in
/-- Slice permutation formulas give one bounded multiplicity operator that
acts on every repeated-letter word. Its definition uses a single unit reference
word, but the conclusion holds for all letters, with no dependence on that word. -/
theorem exists_repeated_operator_of_slice_permutations {n : ℕ}
    (Y : HilbertTensor G (EndpointTensor E F n) →L[ℂ]
      HilbertTensor G (EndpointTensor E F n))
    (Ω : E) (hΩ : ‖Ω‖ = 1) (r₀ : F) (hr₀ : ‖r₀‖ = 1)
    (hslices : ∀ a b : G, ∃ c : PerfectMatching (Fin n ⊕ Fin n) → ℂ,
      multiplicitySlice Y a b = endpointAmplification (crossPairingOperator c)) :
    ∃ B : G →L[ℂ] G, ‖B‖ ≤ ‖Y‖ ∧ ∀ a d r,
      Y (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
        hilbertTensorInsert (B a) (endpointWord d (fun _ : Fin n => r)) := by
  classical
  let w₀ := endpointWord Ω (fun _ : Fin n => r₀)
  have hw₀ : ‖w₀‖ = 1 := norm_endpointWord_constant Ω r₀ hΩ hr₀
  let B := multiplicityCompression Y w₀
  refine ⟨B, norm_multiplicityCompression_le Y w₀ hw₀, ?_⟩
  intro a d r
  apply hilbertTensor_ext_inner_insert
  intro b z
  obtain ⟨c, hc⟩ := hslices a b
  let coefficient := ∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1}, c P.1
  have hact (d : E) (r : F) :
      multiplicitySlice Y a b (endpointWord d (fun _ : Fin n => r)) =
        coefficient • endpointWord d (fun _ : Fin n => r) := by
    simp only [hc, endpointWord, endpointAmplification_insert,
      crossPairingOperator_constant, map_smul, coefficient]
  have hscalar : inner ℂ b (B a) = coefficient := by
    rw [inner_multiplicityCompression]
    change inner ℂ w₀ (multiplicitySlice Y a b
      (endpointWord Ω (fun _ : Fin n => r₀))) = coefficient
    rw [hact, inner_smul_right, inner_self_eq_norm_sq_to_K, hw₀]
    simp
  rw [← inner_multiplicitySlice, hact, inner_smul_right, inner_hilbertTensorInsert, hscalar]

omit [CompleteSpace E] in
/-- The compression along any unit repeated tail recovers the same multiplicity
operator. This gives explicit independence of the reference tail. -/
theorem multiplicityCompression_eq_of_repeated_action {n : ℕ}
    (Y : HilbertTensor G (EndpointTensor E F n) →L[ℂ]
      HilbertTensor G (EndpointTensor E F n)) (B : G →L[ℂ] G)
    (hact : ∀ a d r, Y (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
      hilbertTensorInsert (B a) (endpointWord d (fun _ : Fin n => r)))
    (Ω : E) (hΩ : ‖Ω‖ = 1) (r : F) (hr : ‖r‖ = 1) :
    multiplicityCompression Y (endpointWord Ω (fun _ : Fin n => r)) = B := by
  ext a
  apply ext_inner_left ℂ
  intro b
  rw [inner_multiplicityCompression, inner_multiplicitySlice, hact, inner_hilbertTensorInsert,
    inner_self_eq_norm_sq_to_K, norm_endpointWord_constant Ω r hΩ hr]
  simp

variable {α : Type*} [Fintype α] [DecidableEq α] {k l : ℕ}

variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- On equal levels a bounded operator on the multiplicity factor acts on
all repeated-letter words, independently of the unit repeated letter. -/
theorem exists_multiplicity_repeated_operator_of_schurWeyl {n : ℕ}
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : HilbertTensor G (EndpointTensor E F n) →L[ℂ]
      HilbertTensor G (EndpointTensor E F n))
    (hleft : ∀ s a, Y.comp (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a))) =
      (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a))).comp Y)
    (cov : ∀ s, MultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin n ⊕ Fin n)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin n ⊕ Fin n))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin n ⊕ Fin n) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) :
    ∃ B : G →L[ℂ] G, ‖B‖ ≤ ‖Y‖ ∧ ∀ a d r,
      Y (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
        hilbertTensorInsert (B a) (endpointWord d (fun _ : Fin n => r)) := by
  apply exists_repeated_operator_of_slice_permutations Y T.traceVector T.norm_traceVector
    (T.realOrthonormal 0) (T.realOrthonormal_orthonormal.norm_eq_one 0)
  intro a b
  exact endpoint_intertwiner_permutations_of_schurWeyl T (multiplicitySlice Y a b)
    (fun s c => multiplicitySlice_intertwines Y _ _ (hleft s c) a b)
    (fun s => (cov s).slice a b) spanning hcontraction labels hlabels

end EndpointMultiplicity

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordLevelClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Different multiplicities and the orthogonal word-level decomposition

Source and target word levels have independent Hilbert multiplicity spaces.
Their scalar slices are bounded endpoint intertwiners, so unequal degrees
vanish by the completed endpoint classification.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {Gsource Gtarget H K : Type*}
  [NormedAddCommGroup Gsource] [InnerProductSpace ℂ Gsource]
  [NormedAddCommGroup Gtarget] [InnerProductSpace ℂ Gtarget]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Cross-multiplicity slices are the actual elementary tensor coefficients. -/
theorem inner_crossMultiplicitySlice
    (Y : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (a : Gsource) (b : Gtarget) (x : H) (z : K) :
    inner ℂ z (crossMultiplicitySlice Y a b x) =
      inner ℂ (hilbertTensorInsert b z) (Y (hilbertTensorInsert a x)) := by
  change inner ℂ z (tensorSlice b (Y (hilbertTensorInsert a x))) = _
  generalize Y (hilbertTensorInsert a x) = w
  induction w using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih w =>
    induction w using OAI.tensorInductionOn with
    | tmul c y =>
      change inner ℂ z (tensorSlice b (hilbertTensorInsert c y)) =
        inner ℂ (hilbertTensorInsert b z) (hilbertTensorInsert c y)
      rw [tensorSlice_insert, inner_smul_right, inner_hilbertTensorInsert]
    | add u v hu hv =>
      have hs : tensorSlice b ((u + v : Gtarget ⊗[ℂ] K) : HilbertTensor Gtarget K) =
          tensorSlice b (u : HilbertTensor Gtarget K) + tensorSlice b (v : HilbertTensor Gtarget K) :=
        (congrArg (tensorSlice b) (hilbertTensor_coe_add u v)).trans
          ((tensorSlice b).map_add _ _)
      calc
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor Gtarget K) +
              tensorSlice b (v : HilbertTensor Gtarget K)) := congrArg (fun y => inner ℂ z y) hs
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor Gtarget K)) +
              inner ℂ z (tensorSlice b (v : HilbertTensor Gtarget K)) := inner_add_right _ _ _
        _ = inner ℂ (hilbertTensorInsert b z) (u : HilbertTensor Gtarget K) +
              inner ℂ (hilbertTensorInsert b z) (v : HilbertTensor Gtarget K) := congrArg₂ (· + ·) hu hv
        _ = _ := ((congrArg (fun y => inner ℂ (hilbertTensorInsert b z) y)
            (hilbertTensor_coe_add u v)).trans (inner_add_right _ _ _)).symm

/-- All cross-multiplicity slices determine the entire bounded operator. -/
theorem crossMultiplicitySlice_ext
    (Y Z : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (hslice : ∀ a b, crossMultiplicitySlice Y a b = crossMultiplicitySlice Z a b) : Y = Z := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  apply hilbertTensor_ext_inner_insert
  intro b z
  rw [← inner_crossMultiplicitySlice, ← inner_crossMultiplicitySlice, hslice]

section EndpointLevels

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {α : Type*} [Fintype α] [DecidableEq α] {k l : ℕ}

variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- The unequal-degree theorem applies with entirely different source and
target multiplicity Hilbert spaces. -/
theorem crossMultiplicity_intertwiner_zero_of_schurWeyl
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : HilbertTensor Gsource (EndpointTensor E F k) →L[ℂ]
      HilbertTensor Gtarget (EndpointTensor E F l))
    (hleft : ∀ s a,
      Y.comp (hilbertTensorLift (endpointHeadAction (n := k) ((T.stage s).left a))) =
      (hilbertTensorLift (endpointHeadAction (n := l) ((T.stage s).left a))).comp Y)
    (cov : ∀ s, CrossMultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (hkl : k ≠ l) : Y = 0 := by
  apply crossMultiplicitySlice_ext
  intro a b
  rw [crossMultiplicitySlice_zero]
  exact endpoint_intertwiner_zero_of_schurWeyl T (crossMultiplicitySlice Y a b)
    (fun s c => crossMultiplicitySlice_intertwines Y _ _ (hleft s c) a b)
    (fun s => (cov s).slice a b) spanning hcontraction labels hlabels hkl

end EndpointLevels

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_OrthogonalWordLevels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal word-level inclusions turn the proved off-diagonal block
vanishing into actual preservation of each full word level. -/

noncomputable section
namespace KadisonSimilarity

variable {W : ℕ → Type*} [∀ n, NormedAddCommGroup (W n)]
  [∀ n, InnerProductSpace ℂ (W n)] [∀ n, CompleteSpace (W n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace OrthogonalWordLevels

variable (U : OrthogonalWordLevels W H)

theorem coordinate_inclusion_ne {n m : ℕ} (h : n ≠ m) (x : W m) :
    U.coordinate n (U.inclusion m x) = 0 := by
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((U.inclusion n).toContinuousLinearMap.adjoint (U.inclusion m x)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  exact U.orthogonal n m h y x

omit [∀ n, CompleteSpace (W n)] [CompleteSpace H] in
/-- A continuous linear map is determined by its values on the actual word
inclusions because their linear span is dense. -/
theorem map_eq_zero_of_levels {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (f : H →L[ℂ] K) (hf : ∀ n x, f (U.inclusion n x) = 0) : f = 0 := by
  have hs : Submodule.span ℂ (⋃ n, Set.range (U.inclusion n)) ≤ f.ker := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨n, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact hf n y
  have ht := (Submodule.span ℂ (⋃ n, Set.range (U.inclusion n))).topologicalClosure_minimal
    hs f.isClosed_ker
  rw [U.dense_span] at ht
  ext x
  exact ht (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))

/-- All word-level coordinates separate vectors in the ambient Hilbert space. -/
theorem eq_zero_of_coordinates (z : H) (hz : ∀ n, U.coordinate n z = 0) : z = 0 := by
  have hf : innerSL ℂ z = 0 := U.map_eq_zero_of_levels (innerSL ℂ z) (by
    intro n x
    apply inner_eq_zero_symm.mp
    change inner ℂ ((U.inclusion n).toContinuousLinearMap x) z = 0
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x (U.coordinate n z) = 0
    rw [hz, inner_zero_right])
  exact inner_self_eq_zero.mp (congrArg (fun f : H →L[ℂ] ℂ => f z) hf)

/-- Vanishing of the off-diagonal blocks implies actual preservation of every
word level; this uses dense span, rather than an assumed direct-sum model. -/
theorem preserves_of_offDiagonal_zero (Y : H →L[ℂ] H)
    (hzero : ∀ m n, m ≠ n → U.block Y m n = 0) (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) := by
  ext x
  change Y (U.inclusion n x) = U.inclusion n (U.block Y n n x)
  apply sub_eq_zero.mp
  apply U.eq_zero_of_coordinates
  intro m
  rw [map_sub]
  by_cases hmn : m = n
  · subst m
    rw [U.coordinate_inclusion_self]
    exact sub_self _
  · rw [U.coordinate_inclusion_ne hmn, sub_zero]
    change U.block Y m n x = 0
    rw [hzero m n hmn]
    rfl

end OrthogonalWordLevels

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordLevelRepeatedOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical multiplicity operators on repeated-letter words

Compression to one normalized repeated word defines the degree-wise operator.
The invariant-intertwiner classification proves that this same operator acts
on every repeated-letter word. Adjoint compatibility follows from the concrete
compression formula.
-/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)

omit [∀ s, Nonempty (A s)] in
/-- The canonical compression commutes with taking the adjoint, for every
bounded ambient operator, before any invariant-theory hypotheses are imposed. -/
theorem wordLevelRepeatedOperator_adjoint (Y : H →L[ℂ] H) (n : ℕ) :
    wordLevelRepeatedOperator T U Y.adjoint n = (wordLevelRepeatedOperator T U Y n).adjoint := by
  simp only [wordLevelRepeatedOperator, multiplicityCompression,
    OrthogonalWordLevels.block, OrthogonalWordLevels.coordinate,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

variable (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)

include hleft hunitary in
/-- The degree-wise compression acts on every repeated-letter vector in its
full diagonal block. -/
theorem wordLevelRepeatedOperator_block_apply (n : ℕ)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin n ⊕ Fin n)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin n ⊕ Fin n))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin n ⊕ Fin n) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (a : G n) (d : E) (r : F) :
    U.block Y n n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
      hilbertTensorInsert (wordLevelRepeatedOperator T U Y n a)
        (endpointWord d (fun _ : Fin n => r)) := by
  obtain ⟨B, _, hB⟩ := exists_multiplicity_repeated_operator_of_schurWeyl T (U.block Y n n)
    (fun s c => U.block_intertwines Y (C.leftAction s c) _ _ (hleft s c)
      (C.left_inclusion s c n) (C.left_adjoint_inclusion s c n))
    (fun s => WordLevelMatrixActions.diagonalCovariance T U C Y hunitary s n)
    spanning hcontraction labels hlabels
  have heq : wordLevelRepeatedOperator T U Y n = B :=
    multiplicityCompression_eq_of_repeated_action (U.block Y n n) B hB
      T.traceVector T.norm_traceVector (T.realOrthonormal 0)
      (T.realOrthonormal_orthonormal.norm_eq_one 0)
  rw [heq]
  exact hB a d r

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorMatrixAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite tensor matrices and the invariance of permutation contractions.
These coordinate calculations supply the spanning generators for the local
Schur--Weyl argument. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem tupleTensorMatrix_mul (v w : ι → Matrix α α ℂ) :
    tupleTensorMatrix (fun i => v i * w i) = tupleTensorMatrix v * tupleTensorMatrix w := by
  ext f g
  simp only [tupleTensorMatrix_apply, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum fun i a => v i (f i) a * w i a (g i)

theorem tensorMatrix_mul_permutation (v : ι → Matrix α α ℂ) (π : Equiv.Perm ι)
    (f g : ι → α) :
    (tupleTensorMatrix v * tensorPermutationMatrix π : Matrix (ι → α) (ι → α) ℂ) f g =
      tupleTensorMatrix v f (tensorCoordinatePermutation π g) := by
  simp [Matrix.mul_apply, tensorPermutationMatrix]

theorem permutation_mul_tensorMatrix (v : ι → Matrix α α ℂ) (π : Equiv.Perm ι)
    (f g : ι → α) :
    (tensorPermutationMatrix π * tupleTensorMatrix v : Matrix (ι → α) (ι → α) ℂ) f g =
      tupleTensorMatrix v ((tensorCoordinatePermutation π).symm f) g := by
  simp [Matrix.mul_apply, tensorPermutationMatrix, ← Equiv.symm_apply_eq]

theorem constant_tensorMatrix_commutes_permutation (a : Matrix α α ℂ)
    (π : Equiv.Perm ι) :
    tupleTensorMatrix (fun _ : ι => a) * tensorPermutationMatrix π =
      tensorPermutationMatrix π * tupleTensorMatrix (fun _ : ι => a) := by
  ext f g
  rw [tensorMatrix_mul_permutation, permutation_mul_tensorMatrix]
  change (∏ i, a (f i) (g (π i))) = ∏ i, a (f (π.symm i)) (g i)
  simpa using Equiv.prod_comp π (fun i => a (f (π.symm i)) (g i))

theorem permutationContraction_eq_trace (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) :
    permutationContraction π v =
      Matrix.trace (tupleTensorMatrix v * tensorPermutationMatrix π) := by
  simp only [Matrix.trace, Matrix.diag, tensorMatrix_mul_permutation]
  rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorCoefficientMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.star_tensorMatrixUnit _root_.OAI.KadisonSimilarity.tensorMatrixUnit_eq_single _root_.OAI.KadisonSimilarity.tensorMatrixUnit_mul _root_.OAI.KadisonSimilarity.trace_tensorMatrixUnit _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trace-pairing bridge from invariant multilinear forms to the
commutant of finite tensor powers. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [Fintype ι] [DecidableEq ι] [Fintype α] in
theorem tensorMatrixUnit_as_single (a b : α) :
    tensorMatrixUnit a b = Matrix.single a b (1 : ℂ) := by
  ext r c
  simp only [tensorMatrixUnit_apply, Matrix.single_apply, eq_comm]

theorem matrix_eq_sum_tensorMatrixUnit (a : Matrix α α ℂ) :
    a = ∑ r, ∑ c, a r c • tensorMatrixUnit r c := by
  simpa only [tensorMatrixUnit_as_single, Matrix.smul_single, smul_eq_mul, mul_one] using
    Matrix.matrix_eq_sum_single a

/-- Expansion in matrix units, keeping one row and column label per slot. -/
theorem multilinear_matrix_expansion
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ)
    (v : ι → Matrix α α ℂ) :
    F v = ∑ r : ι → α, ∑ c : ι → α,
      (∏ i, v i (r i) (c i)) * F (fun i => tensorMatrixUnit (r i) (c i)) := by
  have hv : v = fun i => ∑ r, ∑ c, v i r c • tensorMatrixUnit r c := by
    funext i
    exact matrix_eq_sum_tensorMatrixUnit (v i)
  conv_lhs => rw [hv]
  rw [F.map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [F.map_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact F.map_smul_univ (fun i => v i (r i) (c i))
    (fun i => tensorMatrixUnit (r i) (c i))

theorem multilinear_eq_trace_tensorCoefficient
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ)
    (v : ι → Matrix α α ℂ) :
    F v = Matrix.trace (tensorCoefficientMatrix F * tupleTensorMatrix v) := by
  rw [multilinear_matrix_expansion]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    tensorCoefficientMatrix, Matrix.of_apply, tupleTensorMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

omit [DecidableEq ι] [Fintype α] in
theorem tupleTensorMatrix_matrixUnits (r c : ι → α) :
    tupleTensorMatrix (fun i => tensorMatrixUnit (r i) (c i)) =
      Matrix.single r c (1 : ℂ) := by
  ext f g
  simp only [tupleTensorMatrix_apply, tensorMatrixUnit_apply, Fintype.prod_boole,
    Matrix.single_apply]
  congr 1
  apply propext
  simp only [forall_and, funext_iff, eq_comm]

/-- Tensor products of matrix units separate the trace pairing. -/
theorem eq_of_trace_tupleTensorMatrix_eq (A B : Matrix (ι → α) (ι → α) ℂ)
    (h : ∀ v : ι → Matrix α α ℂ,
      Matrix.trace (A * tupleTensorMatrix v) = Matrix.trace (B * tupleTensorMatrix v)) : A = B := by
  ext f g
  have hfg := h (fun i => tensorMatrixUnit (g i) (f i))
  rw [tupleTensorMatrix_matrixUnits] at hfg
  simpa [Matrix.trace_mul_single] using hfg

/-- An invariant form has a trace-dual matrix commuting with every tensor
power of a unitary. -/
theorem tensorCoefficientMatrix_commutes_unitary
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ)
    (hF : UnitaryConjugationInvariant F) (u : Matrix.unitaryGroup α ℂ) :
    tensorCoefficientMatrix F * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
      tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * tensorCoefficientMatrix F := by
  let U := tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ))
  let C := tensorCoefficientMatrix F
  have hU : U * star U = 1 := by
    rw [← tupleTensorMatrix_star, ← tupleTensorMatrix_mul]
    simpa only [u.property.2] using (tupleTensorMatrix_one (ι := ι) (α := α))
  have hC : star U * C * U = C := by
    apply eq_of_trace_tupleTensorMatrix_eq
    intro v
    have h := hF u v
    simp only [multilinear_eq_trace_tensorCoefficient, tupleTensorMatrix_mul,
      tupleTensorMatrix_star] at h
    change Matrix.trace (C * (U * tupleTensorMatrix v * star U)) =
      Matrix.trace (C * tupleTensorMatrix v) at h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle] at h
    simpa only [Matrix.mul_assoc] using h
  change C * U = U * C
  calc
    C * U = (U * star U) * (C * U) := by rw [hU, Matrix.one_mul]
    _ = U * (star U * C * U) := by simp only [Matrix.mul_assoc]
    _ = U * C := by rw [hC]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorDiagonalWeights
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal unitary phases separate the multiplicity weights of a finite
tensor power. This is the weight calculation in the Schur--Weyl argument. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [DecidableEq ι] [Fintype α] in
theorem tensorLabelCount_le (f : ι → α) (a : α) :
    tensorLabelCount f a ≤ Fintype.card ι := Fintype.card_subtype_le _

omit [DecidableEq ι] in
theorem prod_labels_eq (f : ι → α) (d : α → ℂ) :
    (∏ i, d (f i)) = ∏ a, d a ^ tensorLabelCount f a := by
  rw [← Fintype.prod_fiberwise' f d]
  simp only [Finset.prod_const, Finset.card_univ, tensorLabelCount]

omit [DecidableEq ι] [Fintype α] in
theorem tupleTensorMatrix_diagonal (d : α → ℂ) :
    tupleTensorMatrix (fun _ : ι => Matrix.diagonal d) =
      Matrix.diagonal (fun f : ι → α => ∏ i, d (f i)) := by
  ext f g
  simp only [tupleTensorMatrix_apply, Matrix.diagonal_apply, Fintype.prod_ite_zero]
  congr 1
  exact propext funext_iff.symm

omit [DecidableEq ι] in
private theorem phase_product (f : ι → α) (a : α) (z : ℂ) :
    (∏ i, if f i = a then z else 1) = z ^ tensorLabelCount f a := by
  rw [prod_labels_eq f (fun b => if b = a then z else 1)]
  simp only [ite_pow, one_pow]
  simp

/-- Distinct label multiplicities cannot occur in the support of an operator
commuting with all tensor powers of unitaries. -/
theorem tensor_commutant_entry_zero_of_weight_ne
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (f g : ι → α) (a : α) (hne : tensorLabelCount f a ≠ tensorLabelCount g a) :
    C f g = 0 := by
  let n := Fintype.card ι + 1
  let z := tensorRoot n
  let d : α → unitary ℂ := fun b => if b = a then z else 1
  have hp : IsPrimitiveRoot (z : ℂ) n := Complex.isPrimitiveRoot_exp n (by dsimp [n]; omega)
  have hfg := congrArg (fun M : Matrix (ι → α) (ι → α) ℂ => M f g)
    (hC (tensorDiagonalUnitary d))
  change (C * tupleTensorMatrix (fun _ : ι => Matrix.diagonal (fun b => (d b : ℂ)))) f g =
    (tupleTensorMatrix (fun _ : ι => Matrix.diagonal (fun b => (d b : ℂ))) * C) f g at hfg
  rw [tupleTensorMatrix_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hfg
  have hd (r : ι → α) : (∏ i, (d (r i) : ℂ)) = (z : ℂ) ^ tensorLabelCount r a := by
    simpa only [d, apply_ite, OneMemClass.coe_one] using phase_product r a (z : ℂ)
  rw [hd, hd, mul_comm _ (C f g)] at hfg
  by_contra hc
  have heq := mul_left_cancel₀ hc hfg
  exact hne (hp.pow_inj (by have := tensorLabelCount_le g a; dsimp [n]; omega)
    (by have := tensorLabelCount_le f a; dsimp [n]; omega) heq).symm

/-- Every complex diagonal commutes with the tensor commutant; the unit-circle
condition on the testing diagonals has disappeared. -/
theorem tensor_commutant_commutes_diagonal
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (d : α → ℂ) :
    C * tupleTensorMatrix (fun _ : ι => Matrix.diagonal d) =
      tupleTensorMatrix (fun _ : ι => Matrix.diagonal d) * C := by
  rw [tupleTensorMatrix_diagonal]
  ext f g
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ∀ a, tensorLabelCount f a = tensorLabelCount g a
  · rw [prod_labels_eq f, prod_labels_eq g]
    simp_rw [h]
    exact mul_comm _ _
  · obtain ⟨a, ha⟩ := not_forall.mp h
    rw [tensor_commutant_entry_zero_of_weight_ne C hC f g a ha]
    simp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorCommutantExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending a tensor commutation identity from unitary matrices to all
matrices. Diagonal weights, Hermitian diagonalization and a polynomial
identity suffice; no decomposition of a general matrix is assumed. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Commutation with unitary tensor powers implies commutation with every
Hermitian tensor power. -/
theorem tensor_commutant_commutes_hermitian
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (a : Matrix α α ℂ) (ha : a.IsHermitian) :
    C * tupleTensorMatrix (fun _ : ι => a) =
      tupleTensorMatrix (fun _ : ι => a) * C := by
  let u := ha.eigenvectorUnitary
  let d : Matrix α α ℂ := Matrix.diagonal (RCLike.ofReal ∘ ha.eigenvalues : α → ℂ)
  have ha' : a = (u : Matrix α α ℂ) * d * star (u : Matrix α α ℂ) := by
    simpa only [u, d, Unitary.conjStarAlgAut_apply, Unitary.coe_star] using ha.spectral_theorem
  rw [ha', tupleTensorMatrix_mul, tupleTensorMatrix_mul]
  have hu := hC u
  have hs := hC (star u)
  have hd := tensor_commutant_commutes_diagonal C hC (RCLike.ofReal ∘ ha.eigenvalues : α → ℂ)
  change C * (tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) *
      tupleTensorMatrix (fun _ : ι => d) *
      tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ))) = _
  calc
    _ = (C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ))) *
        tupleTensorMatrix (fun _ : ι => d) *
        tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = (tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C) *
        tupleTensorMatrix (fun _ : ι => d) *
        tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ)) := by rw [hu]
    _ = tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) *
        (tupleTensorMatrix (fun _ : ι => d) * C) *
        tupleTensorMatrix (fun _ : ι => star (u : Matrix α α ℂ)) := by
      rw [Matrix.mul_assoc _ C, hd]
    _ = _ := by
      simpa only [← Matrix.mul_assoc, Unitary.coe_star] using congrArg
        (fun X => tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) *
          tupleTensorMatrix (fun _ : ι => d) * X) hs

omit [DecidableEq α] in
private theorem tensorCommutatorPolynomial_eval (C : Matrix (ι → α) (ι → α) ℂ)
    (a b : Matrix α α ℂ) (f g : ι → α) (z : ℂ) :
    (tensorCommutatorPolynomial C a b f g).eval z =
      (C * tupleTensorMatrix (fun _ : ι => a + z • b)) f g -
        (tupleTensorMatrix (fun _ : ι => a + z • b) * C) f g := by
  simp only [tensorCommutatorPolynomial, Polynomial.eval_sub, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Matrix.mul_apply, tupleTensorMatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq α] in
/-- A polynomial commutation identity on a real line also holds on its
complexification. -/
theorem tensor_commutes_complex_line
    (C : Matrix (ι → α) (ι → α) ℂ) (a b : Matrix α α ℂ)
    (h : ∀ t : ℝ,
      C * tupleTensorMatrix (fun _ : ι => a + (t : ℂ) • b) =
        tupleTensorMatrix (fun _ : ι => a + (t : ℂ) • b) * C)
    (z : ℂ) :
    C * tupleTensorMatrix (fun _ : ι => a + z • b) =
      tupleTensorMatrix (fun _ : ι => a + z • b) * C := by
  ext f g
  have hzero : tensorCommutatorPolynomial C a b f g = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro _ ⟨t, rfl⟩
    change (tensorCommutatorPolynomial C a b f g).eval (t : ℂ) = 0
    rw [tensorCommutatorPolynomial_eval, h t, sub_self]
  have hz := congrArg (Polynomial.eval z) hzero
  simpa only [tensorCommutatorPolynomial_eval, Polynomial.eval_zero, sub_eq_zero] using hz

/-- The exact unitary-to-all-matrices extension needed for finite tensor
Schur--Weyl spanning. -/
theorem tensor_commutant_commutes_matrix
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C)
    (a : Matrix α α ℂ) :
    C * tupleTensorMatrix (fun _ : ι => a) =
      tupleTensorMatrix (fun _ : ι => a) * C := by
  have hre : (realPart a : Matrix α α ℂ).IsHermitian := (realPart a).property
  have him : (imaginaryPart a : Matrix α α ℂ).IsHermitian := (imaginaryPart a).property
  have hline (t : ℝ) := tensor_commutant_commutes_hermitian C hC
    ((realPart a : Matrix α α ℂ) + (t : ℂ) • (imaginaryPart a : Matrix α α ℂ))
    (hre.add (him.smul (by change star (t : ℂ) = (t : ℂ); simp)))
  have he := tensor_commutes_complex_line C (realPart a) (imaginaryPart a) hline Complex.I
  simpa only [realPart_add_I_smul_imaginaryPart] using he

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorStableSpanning
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur--Weyl spanning in the stable range needed after taking a cofinal
tail of the matrix tower. The proof uses a single column with distinct labels. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [DecidableEq ι] [Fintype α] in
theorem exists_permutation_of_tensor_weights
    (j : ι → α) (hj : Function.Injective j) (f : ι → α)
    (h : ∀ a, tensorLabelCount f a = tensorLabelCount j a) :
    ∃ π : Equiv.Perm ι, f = tensorCoordinatePermutation π j := by
  have he (i : ι) : ∃ k, j k = f i := by
    have hp : 0 < tensorLabelCount f (f i) :=
      Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
    rw [h] at hp
    obtain ⟨⟨k, hk⟩⟩ := Fintype.card_pos_iff.mp hp
    exact ⟨k, hk⟩
  choose p hp using he
  have hs : Function.Surjective p := by
    intro k
    have hpos : 0 < tensorLabelCount j (j k) :=
      Fintype.card_pos_iff.mpr ⟨⟨k, rfl⟩⟩
    rw [← h] at hpos
    obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨i, hj ((hp i).trans hi)⟩
  let π := Equiv.ofBijective p (Finite.surjective_iff_bijective.mp hs)
  exact ⟨π, funext fun i => (hp i).symm⟩

omit [Fintype α] in
private theorem tensorColumnTransfer_apply
    (j : ι → α) (hj : Function.Injective j) (f : ι → α) (a : α) (i : ι) :
    tensorColumnTransfer j f a (j i) = if a = f i then 1 else 0 := by
  simp [tensorColumnTransfer, Matrix.sum_apply, Matrix.single_apply,
    and_comm, hj.eq_iff, ite_and, eq_comm]

omit [Fintype α] in
private theorem tensorColumnTransfer_column
    (j : ι → α) (hj : Function.Injective j) (f g : ι → α) :
    tupleTensorMatrix (fun _ : ι => tensorColumnTransfer j f) g j =
      if g = f then 1 else 0 := by
  simp only [tupleTensorMatrix_apply, tensorColumnTransfer_apply j hj,
    Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

/-- A matrix commuting with every tensor power is determined by its column
at any elementary tensor whose labels are distinct. -/
theorem tensor_commutant_eq_zero_of_column
    (j : ι → α) (hj : Function.Injective j)
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ a : Matrix α α ℂ,
      C * tupleTensorMatrix (fun _ : ι => a) =
        tupleTensorMatrix (fun _ : ι => a) * C)
    (hcolumn : ∀ f, C f j = 0) : C = 0 := by
  ext f g
  have h := congrArg (fun A : Matrix (ι → α) (ι → α) ℂ => A f j)
    (hC (tensorColumnTransfer j g))
  simp only [Matrix.mul_apply] at h
  simp only [tensorColumnTransfer_column j hj] at h
  simpa [hcolumn] using h

/-- The full tensor commutant is spanned by coordinate permutations once a
tuple of distinct labels is available. -/
theorem tensor_commutant_spanned_by_permutations
    (j : ι → α) (hj : Function.Injective j)
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C) :
    ∃ c : Equiv.Perm ι → ℂ, C = ∑ π, c π • tensorPermutationMatrix (α := α) π := by
  let c : Equiv.Perm ι → ℂ := fun π => C (tensorCoordinatePermutation π j) j
  let S : Matrix (ι → α) (ι → α) ℂ := ∑ π, c π • tensorPermutationMatrix π
  have hinj : Function.Injective (fun π : Equiv.Perm ι => tensorCoordinatePermutation π j) := by
    intro π ρ h
    apply Equiv.ext
    intro i
    exact hj (congrFun h i)
  have hcolumn (f : ι → α) : C f j = S f j := by
    dsimp only [S]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      tensorPermutationMatrix, Matrix.of_apply]
    change C f j = ∑ π, c π * (if f = tensorCoordinatePermutation π j then 1 else 0)
    by_cases hf : ∃ π : Equiv.Perm ι, f = tensorCoordinatePermutation π j
    · obtain ⟨π, rfl⟩ := hf
      rw [Finset.sum_eq_single π]
      · simp [c]
      · intro ρ _ hρ
        have : tensorCoordinatePermutation π j ≠ tensorCoordinatePermutation ρ j :=
          fun h => hρ (hinj h).symm
        simp [this]
      · simp
    · have hz : C f j = 0 := by
        by_contra hc
        apply hf
        apply exists_permutation_of_tensor_weights j hj f
        intro a
        by_contra ha
        exact hc (tensor_commutant_entry_zero_of_weight_ne C hC f j a ha)
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro π _
      have hne : f ≠ tensorCoordinatePermutation π j := fun h => hf ⟨π, h⟩
      simp only [hne, ite_false, mul_zero]
  have hS (a : Matrix α α ℂ) :
      S * tupleTensorMatrix (fun _ : ι => a) =
        tupleTensorMatrix (fun _ : ι => a) * S := by
    dsimp [S]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      constant_tensorMatrix_commutes_permutation]
  have hz : C - S = 0 := tensor_commutant_eq_zero_of_column j hj (C - S)
    (fun a => by
      rw [Matrix.sub_mul, Matrix.mul_sub, tensor_commutant_commutes_matrix C hC a, hS a])
    (fun f => by simp [Matrix.sub_apply, hcolumn f])
  exact ⟨c, sub_eq_zero.mp hz⟩

/-- The stable-range specialization of the published Schur--Weyl input. -/
theorem schurWeylMultilinearSpanning_of_labels [Nonempty α]
    (j : ι → α) (hj : Function.Injective j) : SchurWeylMultilinearSpanning ι α := by
  intro F hF
  obtain ⟨c, hc⟩ := tensor_commutant_spanned_by_permutations j hj
    (tensorCoefficientMatrix F) (tensorCoefficientMatrix_commutes_unitary F hF)
  refine ⟨fun π => c π * (Fintype.card α : ℂ) ^ permutationCycleCount π, ?_⟩
  intro v
  rw [multilinear_eq_trace_tensorCoefficient, hc, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
    ← permutationContraction_eq_trace]
  have hn : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [normalizedPermutationContraction]
  have hp : (Fintype.card α : ℂ) ^ permutationCycleCount π *
      ((Fintype.card α : ℂ)⁻¹) ^ permutationCycleCount π = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hn, one_pow]
  calc
    _ = c π * ((Fintype.card α : ℂ) ^ permutationCycleCount π *
        ((Fintype.card α : ℂ)⁻¹) ^ permutationCycleCount π) *
        permutationContraction π v := by rw [hp, mul_one]
    _ = _ := by ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CofinalMatrixTowers
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word degrees are fixed before the matrix stage is chosen. Cofinal tails
let each degree start in its own stable range; no single finite stage must
accommodate every number of tensor slots. -/

noncomputable section
namespace KadisonSimilarity

open Filter

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

omit [∀ s, Nonempty (A s)] in
/-- Every fixed finite set of tensor slots has injective labels at all stages
of a sufficiently late tail. -/
theorem TracialMatrixTower.exists_tail_labels
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (ι : Type*) [Fintype ι] :
    ∃ b : ℕ, ∃ labels : ∀ s, ι → A (b + s), ∀ s, Function.Injective (labels s) := by
  classical
  have he := (tendsto_atTop.mp T.size_tendsto) (Fintype.card ι : ℝ)
  obtain ⟨b, hb⟩ := eventually_atTop.mp he
  have hc (s : ℕ) : Fintype.card ι ≤ Fintype.card (A (b + s)) := by
    exact_mod_cast hb (b + s) (Nat.le_add_right b s)
  let labels (s : ℕ) : ι ↪ A (b + s) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hc s))
  exact ⟨b, fun s => labels s, fun s => (labels s).injective⟩

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)
  (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)
  (hcontraction : ∀ k l b s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
    normalizedPermutationContraction π
      (fun i => T.transition b (b + s) (Nat.le_add_right b s) (v i)) =
      normalizedPermutationContraction π v)

omit [∀ n, CompleteSpace (G n)] in
include hleft hunitary hcontraction in
/-- Each off-diagonal degree pair uses its own cofinal stable range. In
particular no fixed finite matrix algebra needs infinitely many labels. -/
theorem cofinal_word_levels_preserved (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) := by
  apply U.preserves_of_offDiagonal_zero Y
  intro l k hkl
  obtain ⟨b, labels, hlabels⟩ := T.exists_tail_labels (Option (Fin k ⊕ Fin l))
  exact crossMultiplicity_intertwiner_zero_of_schurWeyl (T.tail b) (U.block Y l k)
    (fun s a => U.block_intertwines Y (C.leftAction (b + s) a) _ _ (hleft (b + s) a)
      (C.left_inclusion (b + s) a k) (C.left_adjoint_inclusion (b + s) a l))
    (fun s => WordLevelMatrixActions.blockCovariance (T.tail b) U (C.tail T U b) Y
      (fun s a => hunitary (b + s) a) s k l)
    (fun s => schurWeylMultilinearSpanning_of_labels (labels s) (hlabels s)) (hcontraction k l b) labels hlabels (Ne.symm hkl)

include hleft hunitary hcontraction in
/-- Repeated-word action with the finite-label requirement discharged using
the matrix-size limit, separately for each word degree. -/
theorem cofinal_wordLevelRepeatedOperator_apply (n : ℕ) (a : G n) (d : E) (r : F) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (wordLevelRepeatedOperator T U Y n a)
        (endpointWord d (fun _ : Fin n => r))) := by
  obtain ⟨b, labels, hlabels⟩ := T.exists_tail_labels (Option (Fin n ⊕ Fin n))
  have hb := wordLevelRepeatedOperator_block_apply (T.tail b) U (C.tail T U b) Y
    (fun s a => hleft (b + s) a) (fun s a => hunitary (b + s) a) n
    (fun s => schurWeylMultilinearSpanning_of_labels (labels s) (hlabels s)) (hcontraction n n b) labels hlabels a d r
  have hp := congrArg (fun f : MultiplicityWordSpace G E F n →L[ℂ] H =>
    f (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))))
    (cofinal_word_levels_preserved T U C Y hleft hunitary hcontraction n)
  change Y (U.inclusion n _) = U.inclusion n (U.block Y n n _) at hp
  rw [hp]
  exact congrArg (U.inclusion n) hb

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_EmbeddedWordClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cofinal invariant-word classification for actual tracial matrix
embeddings. Finite labels and contraction compatibility are both derived. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hmul : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (S : RealTracialSequence τ)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop)


/-- Raw compatible matrix inclusions supply the contractions on every
cofinal tail and for every fixed pair of word degrees. -/
theorem embedded_word_contractions
    (k l b s : ℕ) (p : Equiv.Perm (Option (Fin k ⊕ Fin l)))
    (a : Option (Fin k ⊕ Fin l) → Matrix (A b) (A b) ℂ) :
    normalizedPermutationContraction p
      (fun i => (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize).transition b (b + s) (Nat.le_add_right b s) (a i)) =
      normalizedPermutationContraction p a :=
  NestedTracialMatrices.normalizedPermutationContraction_inclusion M b (b + s) (Nat.le_add_right b s) p a

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E (centeredSubspace (V 1))) H)
  (C : WordLevelMatrixActions (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s a, Y.comp (C.unitaryAction s a) = (C.unitaryAction s a).comp Y)

include hleft hunitary in
/-- Bundled star and unitary representations give the adjoint repeated-word
identity, with the adjoint of the same canonical multiplicity operator. -/
theorem embedded_wordLevelRepeatedOperator_adjoint_apply
    (leftRep : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (left_eq : ∀ s a, C.leftAction s a = leftRep s a)
    (unitaryRep : ∀ s, Matrix.unitaryGroup (A s) ℂ →* unitary (H →L[ℂ] H))
    (unitary_eq : ∀ s a, C.unitaryAction s a = (unitaryRep s a : H →L[ℂ] H))
    (n : ℕ) (a : G n) (d : E) (r : centeredSubspace (V 1)) :
    Y.adjoint (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((wordLevelRepeatedOperator (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U Y n).adjoint a)
        (endpointWord d (fun _ : Fin n => r))) := by
  have hls (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
      (C.leftAction s a).adjoint = C.leftAction s (star a) := by
    rw [left_eq, left_eq, ← ContinuousLinearMap.star_eq_adjoint, map_star]
  have hus (s : ℕ) (a : Matrix.unitaryGroup (A s) ℂ) :
      (C.unitaryAction s a).adjoint = C.unitaryAction s a⁻¹ := by
    rw [unitary_eq, unitary_eq, ← ContinuousLinearMap.star_eq_adjoint,
      ← Unitary.coe_star, Unitary.star_eq_inv, map_inv]
  have hl (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
      Y.adjoint.comp (C.leftAction s a) = (C.leftAction s a).comp Y.adjoint := by
    apply adjoint_commutes_of_adjoint_commutes
    rw [hls]
    exact hleft s (star a)
  have hu (s : ℕ) (a : Matrix.unitaryGroup (A s) ℂ) :
      Y.adjoint.comp (C.unitaryAction s a) = (C.unitaryAction s a).comp Y.adjoint := by
    apply adjoint_commutes_of_adjoint_commutes
    rw [hus]
    exact hunitary s a⁻¹
  simpa only [wordLevelRepeatedOperator_adjoint] using
    cofinal_wordLevelRepeatedOperator_apply (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U C Y.adjoint hl hu
      (embedded_word_contractions τ V L hinner hmul M htrace S hsize) n a d r

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_EmbeddedWordStructure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word-level structure from actual tracial matrix actions. The application
interface has no abstract covariance record: it contains only represented
matrix actions, their raw word formulas, and commutation. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (S : RealTracialSequence τ)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop)
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)] [∀ n, InnerProductSpace ℂ (J n)]
  [∀ n, CompleteSpace (J n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : OrthogonalWordLevels (MultiplicityWordSpace J E (centeredSubspace (V 1))) H)
  (leftRep : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
  (unitaryRep : ∀ s, Matrix.unitaryGroup (A s) ℂ →* unitary (H →L[ℂ] H))
  (hL : ∀ s a n, (leftRep s a).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n)
        (((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left a))))
  (hU : ∀ s u n, (unitaryRep s u : H →L[ℂ] H).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (tracialMatrixWordAction τ V L (M.embedding s) hinner hleft htrace
        (NestedTracialMatrices.denseRange_vector τ V M) u n).toContinuousLinearMap))
  (Y : H →L[ℂ] H)
  (hYL : ∀ s a, Y.comp (leftRep s a) = (leftRep s a).comp Y)
  (hYU : ∀ s u, Y.comp (unitaryRep s u : H →L[ℂ] H) =
    (unitaryRep s u : H →L[ℂ] H).comp Y)

include hL hU hYL hYU in
/-- Taking adjoints gives the same repeated-word action with the adjoint of
the canonical multiplicity operator; no second covariance input is needed. -/
theorem embedded_actions_adjoint_repeated_word_oai (n : ℕ) (a : J n) (d : E)
    (r : centeredSubspace (V 1)) :
    Y.adjoint (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert
        ((wordLevelRepeatedOperator (tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize)
          U Y n).adjoint a) (endpointWord d (fun _ : Fin n => r))) :=
  embedded_wordLevelRepeatedOperator_adjoint_apply τ V L hinner hleft M htrace S hsize U
    (embeddedWordMatrixActions τ V L hinner hleft M htrace S hsize U leftRep unitaryRep hL hU)
    Y hYL hYU leftRep (fun _ _ => rfl) unitaryRep (fun _ _ => rfl) n a d r

end KadisonSimilarity

end

end OAI
end

theorem solution.{u, v, u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.embedded_actions_adjoint_repeated_word_oai.{u, v, u_1, u_2, u_3} := @OAI.KadisonSimilarity.embedded_actions_adjoint_repeated_word_oai.{u, v, u_1, u_2, u_3}
