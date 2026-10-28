-- Prove2me | solution 1 for OAI.Kadison.isometry_row_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:08:43.010958+00:00
-- url     : https://prove2.me/submissions/185de50d-754b-4c51-aa10-00eae4af6dbe

import Mathlib
import Definitions.Def_OAIQ039C019
import Theorems.Thm_OAI_Kadison_isometry_row_adjoint_comp

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfinite
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

section Isometries

variable (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
  (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0)

include hv in
lemma isometry_row_norm_le_oai : ‖operatorRow h (fun i => (v i : K →L[ℂ] K))‖≤1 := by
  have he := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
    (isometry_row_adjoint_comp P h v hv)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [he x,one_mul]

end Isometries

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.isometry_row_norm_le_oai.{u} := @OAI.Kadison.isometry_row_norm_le_oai.{u}
