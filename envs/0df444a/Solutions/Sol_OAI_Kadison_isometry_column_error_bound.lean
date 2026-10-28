-- Prove2me | solution 1 for OAI.Kadison.isometry_column_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:16:17.650048+00:00
-- url     : https://prove2.me/submissions/80752648-e026-431a-9b08-adbda39df8e7

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C030
import Theorems.Thm_OAI_Kadison_commutator_column_bound

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

lemma columnNorm_sq (v : ι → A) :
    columnNorm v ^ 2 = ‖∑ i, star (v i)*v i‖ := by
  rw [columnNorm,WithCStarModule.pi_norm_sq]
  simp only [WithCStarModule.equiv_symm_pi_apply,WithCStarModule.inner_def,star_star]

lemma columnNorm_nonneg (v : ι → A) : 0 ≤ columnNorm v := norm_nonneg _

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfinite
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

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma operatorRow_adjoint (h : ℕ) (a : Fin h → (K →L[ℂ] K)) :
    (operatorRow h a).adjoint=operatorColumn h (fun i => (a i).adjoint) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,operatorColumn_apply,operatorRow_apply,inner_sum,
    ContinuousLinearMap.adjoint_inner_left]

section Isometries

variable (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
  (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0)

include hv in
lemma isometry_range_sum_projection : IsStarProjection (∑ i,v i*star (v i)) := by
  refine ⟨?_,?_⟩
  · change (∑ i,v i*star (v i))*(∑ i,v i*star (v i))=∑ i,v i*star (v i)
    have he (i j : Fin h) : v i*star (v i)*(v j*star (v j))=
        if i=j then v i*star (v i) else 0 := by
      rw [show v i*star (v i)*(v j*star (v j))=v i*(star (v i)*v j)*star (v j) by noncomm_ring,hv]
      split_ifs with he
      · subst j; simp
      · simp
    simp only [Finset.sum_mul,Finset.mul_sum,he]
    simp
  · change star (∑ i,v i*star (v i))=∑ i,v i*star (v i)
    simp only [star_sum,star_mul,star_star]

include hv in
lemma isometry_star_columnNorm_le : CyclicColumns.columnNorm (fun i => star (v i))≤1 := by
  have hn := IsStarProjection.norm_le _ (isometry_range_sum_projection P h v hv)
  have he := CyclicColumns.columnNorm_sq (fun i => star (v i))
  simp only [star_star] at he
  nlinarith [CyclicColumns.columnNorm_nonneg (fun i => star (v i))]

end Isometries

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfiniteBound
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

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma isometry_column_error_eq (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (Y : K →L[ℂ] K) :
    (diagonalAmplification h Y).comp (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint-
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint.comp Y =
    operatorColumn h (fun i => Y*(star (v i) : K →L[ℂ] K)-(star (v i) : K →L[ℂ] K)*Y) := by
  rw [operatorRow_adjoint]
  ext x i
  change (diagonalAmplification h Y
    (operatorColumn h (fun i => (v i : K →L[ℂ] K).adjoint) x)) i-
      (operatorColumn h (fun i => (v i : K →L[ℂ] K).adjoint) (Y x)) i = _
  rw [diagonalAmplification_apply,operatorColumn_apply,operatorColumn_apply]
  rfl

lemma isometry_column_error_bound_oai (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0) (Y : K →L[ℂ] K) :
    ‖(diagonalAmplification h Y).comp (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint-
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint.comp Y‖ ≤
      4*commutatorSeminorm P Y := by
  rw [isometry_column_error_eq]
  exact commutator_column_bound P Y h (fun i => star (v i)) (isometry_star_columnNorm_le P h v hv)

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.isometry_column_error_bound_oai.{u} := @OAI.Kadison.isometry_column_error_bound_oai.{u}
