-- Prove2me | solution 1 for OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:29:01.521308+00:00
-- url     : https://prove2.me/submissions/2f63b3ed-1b85-4253-b1b7-b4ce21d4ec0d

import Mathlib
import Definitions.Def_OAIQ039C014
import Definitions.Def_OAIQ039C021
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C028
import Theorems.Thm_OAI_Kadison_MatrixGNS_flattenCopies_commutator_norm

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
-- module Solutions.OAIQ039_CM.Commutator_BlockDilationBound
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

namespace Kadison.OperatorAmplification

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]

attribute [local instance] OAI.Kadison.OperatorAmplification.blockDilationIndexDecidableEq
attribute [local instance] OAI.Kadison.OperatorAmplification.blockDilationFinTwoDecidableEq
lemma entry_starHom_matrixRepresentation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix ι ι A) (i j : ι) :
    entry ι (CyclicColumns.matrixRepresentation ρ X) i j=ρ (X i j) := by
  ext x
  change CyclicColumns.matrixAction (fun i j => ρ (X i j)) (single ι j x) i=ρ (X i j) x
  simp only [CyclicColumns.matrixAction_apply, single_apply]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma entry_diagonal_commutator (T : H →L[ℂ] H)
    (X : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) :
    entry ι (diagonal (H:=H) ι T*X-X*diagonal (H:=H) ι T) i j=
      T*entry ι X i j-entry ι X i j*T := by
  ext v
  simp [entry_apply,mul_apply_eq_comp,diagonal_single]

lemma commutator_entry_norm_le (T : H →L[ℂ] H)
    (X : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) :
    ‖T*entry ι X i j-entry ι X i j*T‖≤
      ‖diagonal (H:=H) ι T*X-X*diagonal (H:=H) ι T‖ := by
  rw [←entry_diagonal_commutator]
  exact norm_entry_le ι _ i j

theorem balanced_symmetry_commutator_dominates
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H) (X : A) :
    ‖Y*ρ X-ρ X*Y‖≤
      ‖diagonal (H:=H) (Fin 2) Y*
          CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)-
        CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)*
          diagonal (H:=H) (Fin 2) Y‖ := by
  have he : entry (Fin 2) (CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)) 0 1=ρ X := by
    rw [entry_starHom_matrixRepresentation]
    rfl
  simpa only [he] using commutator_entry_norm_le Y
    (CyclicColumns.matrixRepresentation ρ (BalancedDilation.symmetry X)) (0:Fin 2) 1

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFlattenRepresentation
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

namespace Kadison.MatrixGNS

open OperatorAmplification CyclicColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixFlattenRepresentationIndexDecidableEq_rf79b33_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixGNS.matrixFlattenRepresentationCopiesDecidableEq
theorem flatBalanced_commutator_dominates_oai (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    ‖diagonal (H:=H) ι Y*matrixRepresentation ρ X-
      matrixRepresentation ρ X*diagonal (H:=H) ι Y‖ ≤
    ‖diagonal (H:=H) ((Fin 2)×ι) Y*
        matrixRepresentation ρ (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)-
      matrixRepresentation ρ (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)*
        diagonal (H:=H) ((Fin 2)×ι) Y‖ := by
  have h := balanced_symmetry_commutator_dominates (matrixRepresentation ρ) (diagonal (H:=H) ι Y) X
  rw [flattenCopies_commutator_norm] at h
  exact h

end Kadison.MatrixGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates_oai.{u_1, u_2, u_3} := @OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates_oai.{u_1, u_2, u_3}
