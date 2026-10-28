-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:25:37.501963+00:00
-- url     : https://prove2.me/submissions/cd1c68b2-7ab6-43aa-b7c4-3bb45e86e22e

import Mathlib
import Definitions.Def_OAIQ039C010
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C027
import Theorems.Thm_OAI_Kadison_HilbertPadding_diagonal_commutator_extend

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_compress_le (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    ‖compress V T‖ ≤ ‖T‖ := by
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hv' : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact hv
  calc
    ‖compress V T‖ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖T‖ *
        ‖V.toContinuousLinearMap‖ := (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hv' (norm_nonneg _)) hv (norm_nonneg _)
      (by positivity)
    _ = ‖T‖ := by ring

end Kadison.FreeCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertPadding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_extend_le (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : ‖extend E T‖ ≤ ‖T‖ := by
  have he : ‖E.toContinuousLinearMap‖ ≤ 1 := E.norm_toContinuousLinearMap_le
  have he' : ‖E.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact he
  calc
    _ ≤ ‖E.toContinuousLinearMap‖*‖T‖*‖E.toContinuousLinearMap.adjoint‖ :=
      (opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*‖T‖*1 := mul_le_mul (mul_le_mul_of_nonneg_right he (norm_nonneg _))
      he' (norm_nonneg _) (by positivity)
    _ = ‖T‖ := by ring

lemma compress_extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    FreeCorner.compress E (extend E T)=T := by
  ext x
  change E.toContinuousLinearMap.adjoint (E (T (E.toContinuousLinearMap.adjoint (E x))))=T x
  simp only [FreeCorner.isometry_adjoint_apply]

lemma norm_extend (E : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : ‖extend E T‖=‖T‖ := by
  apply le_antisymm (norm_extend_le E T)
  simpa only [compress_extend] using FreeCorner.norm_compress_le E (extend E T)

open OperatorAmplification

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixPadding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification CyclicColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixPaddingSourceDecidableEq_r00b6c0_1 : DecidableEq ι := Classical.decEq ι
local instance matrixPaddingComplementDecidableEq_r00b6c0_1 : DecidableEq κ := Classical.decEq κ
lemma leftCopies_adjoint_apply (v : SumSpace (H:=H) (ι⊕κ)) :
    (leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint v=
      WithLp.toLp 2 (fun i => v (Sum.inl i)) := by
  apply ext_inner_left ℂ
  intro w
  rw [adjoint_inner_right]
  simp [PiLp.inner_apply,Fintype.sum_sum_type]

lemma representation_padMatrix (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (X : CStarMatrix ι ι A) :
    matrixRepresentation ρ (padMatrix ι κ X)=
      extend (leftCopies (H:=H) ι κ) (matrixRepresentation ρ X) := by
  ext v i
  change matrixAction (fun i j => ρ (padMatrix ι κ X i j)) v i=
    leftCopies (H:=H) ι κ
      (matrixRepresentation ρ X ((leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint v)) i
  rw [leftCopies_adjoint_apply]
  cases i <;> simp [padMatrix,Fintype.sum_sum_type,matrixRepresentation,matrixAction_apply,Matrix.fromBlocks]

theorem matrix_padding_commutator_norm_oai (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (X : CStarMatrix ι ι A) :
    ‖diagonal (H:=H) (ι⊕κ) Y*matrixRepresentation ρ (padMatrix ι κ X)-
        matrixRepresentation ρ (padMatrix ι κ X)*diagonal (H:=H) (ι⊕κ) Y‖=
      ‖diagonal (H:=H) ι Y*matrixRepresentation ρ X-
        matrixRepresentation ρ X*diagonal (H:=H) ι Y‖ := by
  rw [representation_padMatrix,diagonal_commutator_extend,norm_extend]

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm_oai.{u_1, u_2, u_3, u_4}
