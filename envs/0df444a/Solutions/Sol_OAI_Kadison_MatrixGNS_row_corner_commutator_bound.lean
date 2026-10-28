-- Prove2me | solution 1 for OAI.Kadison.MatrixGNS.row_corner_commutator_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:29:46.473705+00:00
-- url     : https://prove2.me/submissions/9e590d7c-1400-48b0-b502-eebc5b8939f3

import Mathlib
import Definitions.Def_OAIQ039C013
import Definitions.Def_OAIQ039C021
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixEntryWOT
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] in
lemma norm_single_eq (i : ι) (x : H) : ‖single ι i x‖=‖x‖ := by
  have he : single ι i x=PiLp.single 2 i x := by
    ext j
    simp [PiLp.single_apply]
  rw [he,PiLp.norm_single]

omit [CompleteSpace H] in
lemma norm_entry_le (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) :
    ‖entry ι T i j‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (entry ι T i j) (norm_nonneg T)
  intro x
  change ‖T (single ι j x) i‖≤‖T‖*‖x‖
  calc
    _ ≤ ‖T (single ι j x)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖*‖single ι j x‖ := T.le_opNorm _
    _ = ‖T‖*‖x‖ := by rw [norm_single_eq]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RowOperator
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

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] in
lemma norm_position_le (i j : ι) (a : H →L[ℂ] H) : ‖position ι i j a‖≤‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro v
  rw [position_apply,norm_single_eq]
  exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg a))

omit [CompleteSpace H] [Fintype ι] in
lemma entry_position (i j : ι) (a : H →L[ℂ] H) :
    entry ι (position ι i j a) i j=a := by
  ext x
  simp

omit [CompleteSpace H] in
lemma norm_position (i j : ι) (a : H →L[ℂ] H) : ‖position ι i j a‖=‖a‖ := by
  apply le_antisymm (norm_position_le ι i j a)
  simpa only [entry_position] using norm_entry_le ι (position ι i j a) i j

lemma diagonal_commutator_position (T a : H →L[ℂ] H) (i j : ι) :
    diagonal (H:=H) ι T*position ι i j a-position ι i j a*diagonal (H:=H) ι T=
      position ι i j (T*a-a*T) := by
  ext v k
  simp only [sub_apply,mul_apply_eq_comp,position_apply,diagonal_single,
    diagonal_apply]
  simp only [single_apply]
  by_cases h : k=i <;> simp [h]

lemma norm_diagonal_commutator_position (T a : H →L[ℂ] H) (i j : ι) :
    ‖diagonal (H:=H) ι T*position ι i j a-position ι i j a*diagonal (H:=H) ι T‖=‖T*a-a*T‖ := by
  rw [diagonal_commutator_position,norm_position]

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixRowCorner
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixRowCornerDecidableEq
lemma rowMatrix_corner (i : ι) (X : CStarMatrix ι ι A) :
    rowMatrix i (1:A)*X*rowMatrix i (1:A)=rowMatrix i (X i i) := by
  ext j k
  simp only [CStarMatrix.mul_apply,rowMatrix_apply]
  by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk]

variable [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma rowMatrix_representation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (i : ι) (a : A) :
    CyclicColumns.matrixRepresentation σ (rowMatrix i a)=
      OperatorAmplification.position ι i i (σ a) := by
  ext v j
  simp only [CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
    StarAlgHom.coe_mk,rowMatrix_apply,OperatorAmplification.position_apply,
    OperatorAmplification.single_apply]
  by_cases hj : j=i <;> simp [hj,apply_ite,ite_apply]

lemma row_corner_commutator_bound_oai (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ a : A,‖T*σ a-σ a*T‖ ≤ c*‖a‖) (i : ι)
    (X : CStarMatrix ι ι A) (hX : rowMatrix i (1:A)*X*rowMatrix i (1:A)=X) :
    ‖OperatorAmplification.diagonal (H:=H) ι T*CyclicColumns.matrixRepresentation σ X-
      CyclicColumns.matrixRepresentation σ X*OperatorAmplification.diagonal (H:=H) ι T‖ ≤ c*‖X‖ := by
  have he : X=rowMatrix i (X i i) := hX.symm.trans (rowMatrix_corner i X)
  calc
    _ = ‖T*σ (X i i)-σ (X i i)*T‖ := by
      conv_lhs => rw [he,rowMatrix_representation,
        OperatorAmplification.norm_diagonal_commutator_position]
    _ ≤ c*‖X i i‖ := hT _
    _ ≤ c*‖X‖ := mul_le_mul_of_nonneg_left CStarMatrix.norm_entry_le_norm hc

end Kadison.MatrixGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.MatrixGNS.row_corner_commutator_bound_oai.{u_1, u_2, u_3} := @OAI.Kadison.MatrixGNS.row_corner_commutator_bound_oai.{u_1, u_2, u_3}
