-- Prove2me | solution 1 for OAI.Kadison.isometry_row_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:08:41.627326+00:00
-- url     : https://prove2.me/submissions/55344d62-d426-4f2d-8d5c-7525fc577edf

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C007
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C019
import Theorems.Thm_OAI_Kadison_isometry_column_error_bound

section
-- module Solutions.OAIQ039_CM.Commutator_MainMatrix
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma diagonalAmplification_adjoint (h : ℕ) (Y : K →L[ℂ] K) :
    (diagonalAmplification h Y).adjoint=diagonalAmplification h Y.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,diagonalAmplification_apply,ContinuousLinearMap.adjoint_inner_left]

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfinite
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
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

lemma commutatorSeminorm_star_le (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    commutatorSeminorm P (star Y) ≤ commutatorSeminorm P Y := by
  apply csSup_le
  · exact ⟨0,0,zero_mem P,by simp,by simp⟩
  rintro r ⟨a,ha,hn,rfl⟩
  have hb := commutator_bound_unitball P Y (star_mem ha) (by simpa using hn)
  calc
    ‖star Y*a-a*star Y‖ = ‖star (star Y*a-a*star Y)‖ := (norm_star _).symm
    _ = ‖star a*Y-Y*star a‖ := by rw [star_sub,star_mul,star_mul,star_star]
    _ = ‖Y*star a-star a*Y‖ := norm_sub_rev _ _
    _ ≤ _ := hb

@[simp] lemma commutatorSeminorm_star (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    commutatorSeminorm P (star Y)=commutatorSeminorm P Y :=
  le_antisymm (commutatorSeminorm_star_le P Y)
    (by simpa using commutatorSeminorm_star_le P (star Y))

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfiniteBound
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
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

lemma isometry_row_error_bound_oai (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0) (Y : K →L[ℂ] K) :
    ‖Y.comp (operatorRow h (fun i => (v i : K →L[ℂ] K)))-
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).comp (diagonalAmplification h Y)‖ ≤
      4*commutatorSeminorm P Y := by
  rw [←adjoint.norm_map]
  simp only [map_sub,adjoint_comp,diagonalAmplification_adjoint]
  rw [norm_sub_rev]
  have hb := isometry_column_error_bound P h v hv Y.adjoint
  simpa only [←star_eq_adjoint,commutatorSeminorm_star] using hb

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.isometry_row_error_bound_oai.{u} := @OAI.Kadison.isometry_row_error_bound_oai.{u}
