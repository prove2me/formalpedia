-- Prove2me | solution 1 for OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:29:23.952629+00:00
-- url     : https://prove2.me/submissions/b2429963-75d7-49e3-891c-07bbf1b07248

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C028

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

lemma norm_conjugation {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (U : K ≃ₗᵢ[ℂ] L) (T : K →L[ℂ] K) : ‖U.conjStarAlgEquiv T‖=‖T‖ :=
  StarAlgEquiv.norm_map U.conjStarAlgEquiv T

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixFlattenRepresentationIndexDecidableEq_rbbf504_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixGNS.matrixFlattenRepresentationCopiesDecidableEq
lemma flattenCopies_diagonal (Y : H →L[ℂ] H) :
    (flattenCopies (H:=H) ι κ).conjStarAlgEquiv
      (diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y))=diagonal (H:=H) (κ×ι) Y := by
  ext v p
  rfl

lemma flattenCopies_matrix (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
    (flattenCopies (H:=H) ι κ).conjStarAlgEquiv
      (matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X)=matrixRepresentation ρ (flatten ι κ X) := by
  ext v p
  change matrixAction (fun i j => matrixRepresentation ρ (X i j))
    ((flattenCopies (H:=H) ι κ).symm v) p.1 p.2=
      matrixAction (fun i j => ρ (flatten ι κ X i j)) v p
  simp only [matrixAction_apply,WithLp.ofLp_sum,Finset.sum_apply,
    Fintype.sum_prod_type,flatten_apply]
  apply Finset.sum_congr rfl
  intro j _
  change matrixAction (fun i k => ρ (X p.1 j i k))
    ((flattenCopies (H:=H) ι κ).symm v j) p.2=_
  simp only [matrixAction_apply,flattenCopies_symm_apply]

lemma flattenCopies_commutator_norm_oai (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
    ‖diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)*
        matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X-
      matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X*
        diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)‖=
    ‖diagonal (H:=H) (κ×ι) Y*matrixRepresentation ρ (flatten ι κ X)-
        matrixRepresentation ρ (flatten ι κ X)*diagonal (H:=H) (κ×ι) Y‖ := by
  have hn := norm_conjugation (flattenCopies (H:=H) ι κ)
    (diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y)*
        matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X-
      matrixRepresentation (ι:=κ) (H:=SumSpace (H:=H) ι) (matrixRepresentation (ι:=ι) ρ) X*
        diagonal (H:=SumSpace (H:=H) ι) κ (diagonal (H:=H) ι Y))
  simpa only [map_sub,map_mul,flattenCopies_diagonal,flattenCopies_matrix] using hn.symm

end Kadison.MatrixGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm_oai.{u_1, u_2, u_3, u_4}
