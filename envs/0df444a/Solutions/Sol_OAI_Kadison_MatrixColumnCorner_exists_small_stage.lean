-- Prove2me | solution 1 for OAI.Kadison.MatrixColumnCorner.exists_small_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:05:52.332784+00:00
-- url     : https://prove2.me/submissions/4b01bd5d-2c61-45da-92df-500024edb03a

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixColumnCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.MatrixColumnCorner

variable {I D : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [CStarAlgebra D]

lemma exists_small_stage_oai (J : ℕ → Type*) [∀ n, Fintype (J n)] [∀ n, Nonempty (J n)]
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (J m)) {β : ℝ} (hβ : 0<β) :
    ∃ n, (Fintype.card (J n) : ℝ)⁻¹ ≤ β := by
  obtain ⟨q,hq⟩ := exists_nat_gt β⁻¹
  obtain ⟨n,_,hn⟩ := hsize 0 q
  refine ⟨n,?_⟩
  have hcard : (0:ℝ)<Fintype.card (J n) := by exact_mod_cast Fintype.card_pos
  apply (inv_le_comm₀ hcard hβ).mpr
  exact hq.le.trans (by exact_mod_cast hn)

end Kadison.MatrixColumnCorner

end

end
end

end OAI
end

theorem solution.{u_3} : type_of% @OAI.Kadison.MatrixColumnCorner.exists_small_stage_oai.{u_3} := @OAI.Kadison.MatrixColumnCorner.exists_small_stage_oai.{u_3}
