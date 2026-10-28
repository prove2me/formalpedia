-- Prove2me | solution 1 for OAI.Kadison.HilbertPadding.diagonal_commutator_extend
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:24:08.178027+00:00
-- url     : https://prove2.me/submissions/ae4bd288-4b46-4aac-8181-e9e98e91a4dd

import Mathlib
import Definitions.Def_OAIQ039C027

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertPadding
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma extend_commutator (E : H →ₗᵢ[ℂ] K) (T a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (hl : b.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp a)
    (hr : E.toContinuousLinearMap.adjoint.comp b=a.comp E.toContinuousLinearMap.adjoint) :
    extend E T*b-b*extend E T=extend E (T*a-a*T) := by
  simp only [extend,mul_def,comp_sub,sub_comp,comp_assoc]
  rw [hr,←comp_assoc b,hl]
  simp only [comp_assoc]

open OperatorAmplification

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance instDecidableEq_solutions_rf0be87_1 : DecidableEq ι := Classical.decEq ι
local instance instDecidableEq_solutions_1_rf0be87_1 : DecidableEq κ := Classical.decEq κ
lemma leftCopies_diagonal (a : H →L[ℂ] H) :
    (diagonal (H:=H) (ι⊕κ) a).comp (leftCopies (H:=H) ι κ).toContinuousLinearMap=
      (leftCopies (H:=H) ι κ).toContinuousLinearMap.comp (diagonal (H:=H) ι a) := by
  ext v i
  cases i <;> simp

lemma adjoint_leftCopies_diagonal (a : H →L[ℂ] H) :
    (leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint.comp (diagonal (H:=H) (ι⊕κ) a)=
      (diagonal (H:=H) ι a).comp (leftCopies (H:=H) ι κ).toContinuousLinearMap.adjoint := by
  have h := congrArg (fun T => T.adjoint) (leftCopies_diagonal ι κ (star a))
  simpa only [adjoint_comp, ←star_eq_adjoint, ←map_star, star_star] using h

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixPadding
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

open OperatorAmplification

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixPaddingSourceDecidableEq_rf0be87_1 : DecidableEq ι := Classical.decEq ι
local instance matrixPaddingComplementDecidableEq_rf0be87_1 : DecidableEq κ := Classical.decEq κ
lemma diagonal_commutator_extend_oai (Y : H →L[ℂ] H)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) :
    diagonal (H:=H) (ι⊕κ) Y*extend (leftCopies ι κ) T-
      extend (leftCopies ι κ) T*diagonal (H:=H) (ι⊕κ) Y=
        extend (leftCopies ι κ) (diagonal (H:=H) ι Y*T-T*diagonal (H:=H) ι Y) := by
  have h := extend_commutator (leftCopies (H:=H) ι κ) T (diagonal (H:=H) ι Y)
    (diagonal (H:=H) (ι⊕κ) Y) (leftCopies_diagonal ι κ Y) (adjoint_leftCopies_diagonal ι κ Y)
  have hn := congrArg Neg.neg h
  simpa only [neg_sub,extend,comp_sub,sub_comp] using hn

end Kadison.HilbertPadding

end

end
end

end OAI
end

theorem solution.{u_2, u_3, u_4} : type_of% @OAI.Kadison.HilbertPadding.diagonal_commutator_extend_oai.{u_2, u_3, u_4} := @OAI.Kadison.HilbertPadding.diagonal_commutator_extend_oai.{u_2, u_3, u_4}
