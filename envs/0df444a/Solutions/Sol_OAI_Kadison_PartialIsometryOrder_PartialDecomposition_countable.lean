-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.PartialDecomposition.countable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:30:30.841745+00:00
-- url     : https://prove2.me/submissions/0280e5ec-6852-4ca4-99b4-e292c2dd24a3

import Mathlib
import Definitions.Def_OAIQ039C029

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalCountability
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

theorem countable_orthogonal_family {I : Type*} (v : I → H)
    (hne : ∀ i,v i≠0) (hortho : ∀ i j,i≠j → inner ℂ (v i) (v j)=0) : Countable I := by
  let B : I → Set H := fun i => Metric.ball (v i) (‖v i‖/2)
  have hdis : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi : dist x (v i)<‖v i‖/2 := hxi
    have hj : dist x (v j)<‖v j‖/2 := hxj
    have hd := dist_triangle (v i) x (v j)
    rw [dist_comm (v i) x] at hd
    have hd' : ‖v i-v j‖ < (‖v i‖+‖v j‖)/2 := by
      rw [←dist_eq_norm]
      linarith
    have hs : ‖v i-v j‖^2=‖v i‖^2+‖v j‖^2 := by
      rw [@norm_sub_sq ℂ,hortho i j hij]
      simp
    have hs' := sq_nonneg (‖v i‖-‖v j‖)
    have hn := norm_pos_iff.mpr (hne i)
    have hn' := norm_pos_iff.mpr (hne j)
    nlinarith [norm_nonneg (v i-v j)]
  exact hdis.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by exact div_pos (norm_pos_iff.mpr (hne i)) (by norm_num))⟩)

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialDecompositionCountable
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.PartialIsometryOrder.PartialDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : PartialDecomposition M p)

theorem countable_oai : Countable D.I := by
  have hx (i : D.I) : ∃ x : H,(D.v i).val x≠0 := by
    by_contra hn
    push Not at hn
    exact D.nonzero i (ContinuousLinearMap.ext hn)
  choose x hx using hx
  apply Kadison.countable_orthogonal_family (fun i => (D.v i).val (x i)) hx
  intro i j hij
  rw [←ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (x i) ((star (D.v i).val*(D.v j).val) (x j))=0
  rw [D.cross i j hij]
  simp

end Kadison.PartialIsometryOrder.PartialDecomposition

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.PartialDecomposition.countable_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.PartialDecomposition.countable_oai.{u_1}
