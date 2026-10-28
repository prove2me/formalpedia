-- Prove2me | solution 1 for OAI.Kadison.SeparableTest.bound_of_separable_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:12:32.098992+00:00
-- url     : https://prove2.me/submissions/df640949-2101-4e5b-9abb-7b101d173170

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C030
import Definitions.Def_OAIQ039C037
import Theorems.Thm_OAI_Kadison_SeparableTest_seminorm_bound
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg

section
-- module Solutions.OAIQ039_CM.Commutator_ReducingMatrix
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

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H),x∈K → σ a x∈K)

lemma matrix_intertwines (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    (matrixOperator h (fun i j => σ (X i j))).comp (matrixInclusion K h).toContinuousLinearMap=
    (matrixInclusion K h).toContinuousLinearMap.comp
      (matrixOperator h (fun i j => restrict σ K hinv (X i j))) := by
  ext x i
  change (matrixOperator h (fun i j => σ (X i j)) (matrixInclusion K h x)) i=
    ((matrixOperator h (fun i j => restrict σ K hinv (X i j)) x) i:H)
  erw [matrixOperator_apply,matrixOperator_apply]
  exact (map_sum K.subtype (fun j => restrict σ K hinv (X i j) (x j)) Finset.univ).symm

lemma restricted_matrix_norm_le (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    ‖matrixOperator h (fun i j => restrict σ K hinv (X i j))‖≤
      ‖matrixOperator h (fun i j => σ (X i j))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he := congrArg (fun T => T x) (matrix_intertwines σ K hinv h X)
  change matrixOperator h (fun i j => σ (X i j)) (matrixInclusion K h x)=
    matrixInclusion K h (matrixOperator h (fun i j => restrict σ K hinv (X i j)) x) at he
  rw [←(matrixInclusion K h).norm_map,←he]
  simpa only [LinearIsometry.norm_map] using
    (matrixOperator h (fun i j => σ (X i j))).le_opNorm (matrixInclusion K h x)

omit [CompleteSpace H] [CompleteSpace K] in
lemma diagonal_intertwines (Y : H →L[ℂ] H) (hY : ∀ x∈K,Y x∈K) (h : ℕ) :
    (diagonalAmplification h Y).comp (matrixInclusion K h).toContinuousLinearMap=
      (matrixInclusion K h).toContinuousLinearMap.comp (diagonalAmplification h (Y.restrict hY)) := by
  ext x i
  rfl

lemma matrix_commutator_intertwines (Y : H →L[ℂ] H) (hY : ∀ x∈K,Y x∈K)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    (diagonalAmplification h Y*matrixOperator h (fun i j => σ (X i j))-
      matrixOperator h (fun i j => σ (X i j))*diagonalAmplification h Y).comp
        (matrixInclusion K h).toContinuousLinearMap=
    (matrixInclusion K h).toContinuousLinearMap.comp
      (diagonalAmplification h (Y.restrict hY)*matrixOperator h (fun i j => restrict σ K hinv (X i j))-
       matrixOperator h (fun i j => restrict σ K hinv (X i j))*diagonalAmplification h (Y.restrict hY)) := by
  simp only [sub_comp,comp_sub,mul_def]
  congr 1
  · rw [comp_assoc,matrix_intertwines σ K hinv h X,←comp_assoc,
      diagonal_intertwines K Y hY h,comp_assoc]
  · rw [comp_assoc,diagonal_intertwines K Y hY h,←comp_assoc,
      matrix_intertwines σ K hinv h X,comp_assoc]

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableTestGeometry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.SeparableTest

open SeparableReducingHull ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (Y : H →L[ℂ] H)

variable (ξ : PiLp 2 (fun _ : Fin h => H))

lemma include_vector : matrixInclusion (space h X Y ξ) h (vector h X Y ξ)=ξ := by ext i; rfl

lemma vector_norm : ‖vector h X Y ξ‖=‖ξ‖ := by
  rw [←(matrixInclusion (space h X Y ξ) h).norm_map,include_vector]

lemma matrix_norm_le : ‖matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))‖≤
    ‖matrixOperator h X‖ :=
  restricted_matrix_norm_le (algebra h X).subtype (space h X Y ξ)
    (algebra_invariant h X Y ξ) h (entries h X)

lemma commutator_vector :
    (diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y) ξ=
    matrixInclusion (space h X Y ξ) h
      ((diagonalAmplification h (restrictedY h X Y ξ)*
        matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))-
        matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))*
        diagonalAmplification h (restrictedY h X Y ξ)) (vector h X Y ξ)) := by
  have hh := congrArg (fun L => L (vector h X Y ξ))
    (matrix_commutator_intertwines (algebra h X).subtype (space h X Y ξ)
      (algebra_invariant h X Y ξ) Y (Y_invariant h X Y ξ) h (entries h X))
  change (diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y)
      (matrixInclusion (space h X Y ξ) h (vector h X Y ξ))=_ at hh
  rw [include_vector] at hh
  exact hh

end Kadison.SeparableTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableBoundTransfer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison.SeparableTest

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (h : ℕ)
  (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P)

include hX

lemma bound_on_vector {c : ℝ} (hc : 0 ≤ c) (ξ : PiLp 2 (fun _ : Fin h => H))
    (hb : ‖diagonalAmplification h (restrictedY h X Y ξ)*
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))-
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))*
      diagonalAmplification h (restrictedY h X Y ξ)‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range)
        (restrictedY h X Y ξ)*
      ‖matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))‖) :
    ‖(diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y) ξ‖≤
      (c*commutatorSeminorm P Y*‖matrixOperator h X‖)*‖ξ‖ := by
  let σ := representation h X Y ξ
  let Z := restrictedY h X Y ξ
  let X₀ := fun i j => σ (entries h X i j)
  have hb' : ‖diagonalAmplification h Z*matrixOperator h X₀-
      matrixOperator h X₀*diagonalAmplification h Z‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
    hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left (seminorm_bound h X Y ξ P hX) hc)
      (matrix_norm_le h X Y ξ) (norm_nonneg (matrixOperator h X₀))
      (mul_nonneg hc (commutatorSeminorm_nonneg P Y)))
  rw [commutator_vector h X Y ξ,LinearIsometry.norm_map]
  exact ((diagonalAmplification h Z*matrixOperator h X₀-
    matrixOperator h X₀*diagonalAmplification h Z).le_opNorm (vector h X Y ξ)).trans
      (by rw [vector_norm]; exact mul_le_mul_of_nonneg_right hb' (norm_nonneg ξ))

omit hX in
lemma SeparableBound.on_range {c : ℝ} (hsep : SeparableBound.{u} c)
    {A K : Type u} [CStarAlgebra A] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Z : K →L[ℂ] K) (h : ℕ) (hh : 1≤h)
    (W : Matrix (Fin h) (Fin h) A) :
    ‖diagonalAmplification h Z*matrixOperator h (fun i j => σ (W i j))-
      matrixOperator h (fun i j => σ (W i j))*diagonalAmplification h Z‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant σ.range) Z*
        ‖matrixOperator h (fun i j => σ (W i j))‖ := by
  apply hsep K _ Z h hh
  intro i j
  exact NormalGNS.subset_bicommutant σ.range ⟨W i j,rfl⟩

omit hX in
lemma restricted_bound {c : ℝ} (hsep : SeparableBound.{u} c) (hh : 1≤h)
    (ξ : PiLp 2 (fun _ : Fin h => H)) :
    ‖diagonalAmplification h (restrictedY h X Y ξ)*
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))-
      matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))*
      diagonalAmplification h (restrictedY h X Y ξ)‖≤
      c*commutatorSeminorm (NormalGNS.bicommutant (representation h X Y ξ).range)
        (restrictedY h X Y ξ)*
      ‖matrixOperator h (fun i j => representation h X Y ξ (entries h X i j))‖ := by
  exact hsep.on_range (representation h X Y ξ) (restrictedY h X Y ξ) h hh (entries h X)

theorem bound_of_separable_bound_oai {c : ℝ} (hc : 0 ≤ c)
    (hsep : SeparableBound.{u} c) (hh : 1≤h) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hc (commutatorSeminorm_nonneg P Y)) (norm_nonneg _))
  intro ξ
  exact bound_on_vector P Y h X hX hc ξ (restricted_bound Y h X hsep hh ξ)

end Kadison.SeparableTest

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.SeparableTest.bound_of_separable_bound_oai.{u} := @OAI.Kadison.SeparableTest.bound_of_separable_bound_oai.{u}
