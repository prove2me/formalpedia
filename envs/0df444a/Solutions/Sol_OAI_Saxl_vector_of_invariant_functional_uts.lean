-- Prove2me | solution 1 for OAI.Saxl.vector_of_invariant_functional_uts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:11:03.12895+00:00
-- url     : https://prove2.me/submissions/3bd5bdf8-6a36-4cf6-91ac-a8dc76332150

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006

section
-- module Solutions.OAIQ259_US.Saxl_YoungRule
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/

lemma vector_of_invariant_functional_uts_oai {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (l : Module.Dual ℂ (Specht t)) (hl : l ≠ 0)
    (he : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ∀ x, l (spechtRep t g x) = l x) :
    ∃ y : Specht t, y ≠ 0 ∧ ∀ g : Equiv.Perm (Fin n), a ∘ g = a → spechtRep t g y = y := by
  let e := spechtSelfDual t
  refine ⟨e.symm l, ?_, ?_⟩
  · intro hz
    exact hl (e.symm.injective (hz.trans (map_zero _).symm))
  · intro g hg
    have hi : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a := by
      funext i
      have hh := congrFun hg (g⁻¹ i)
      simpa using hh.symm
    have hdual : (spechtRep t).dual g l = l := by
      apply LinearMap.ext
      intro x
      exact he g⁻¹ hi x
    have hh := LinearMap.congr_fun (e.symm.isIntertwining' g) l
    change e.symm ((spechtRep t).dual g l) = spechtRep t g (e.symm l) at hh
    rw [hdual] at hh
    exact hh.symm

/- Young's sufficiency in the exact form needed for the repeated-row quotient:
a dominant Specht has a nonzero invariant functional for a word of the
prescribed content. -/

end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.vector_of_invariant_functional_uts_oai := @OAI.Saxl.vector_of_invariant_functional_uts_oai
