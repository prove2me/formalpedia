-- Prove2me | solution 1 for OAI.Kadison.isometry_row_adjoint_comp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:34.428011+00:00
-- url     : https://prove2.me/submissions/9827d639-6c15-41fc-864f-946b7801bebb

import Mathlib
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C019

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

lemma operatorRow_adjoint (h : ℕ) (a : Fin h → (K →L[ℂ] K)) :
    (operatorRow h a).adjoint=operatorColumn h (fun i => (a i).adjoint) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,operatorColumn_apply,operatorRow_apply,inner_sum,
    ContinuousLinearMap.adjoint_inner_left]

section Isometries

variable (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
  (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0)

include hv in
lemma isometry_row_adjoint_comp_oai :
    (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint.comp
      (operatorRow h (fun i => (v i : K →L[ℂ] K)))=ContinuousLinearMap.id ℂ _ := by
  rw [operatorRow_adjoint]
  ext x i
  change (operatorColumn h (fun j => (v j : K →L[ℂ] K).adjoint)
    (operatorRow h (fun j => (v j : K →L[ℂ] K)) x)) i=x i
  rw [operatorColumn_apply,operatorRow_apply,map_sum]
  have he (j : Fin h) : (v i : K →L[ℂ] K).adjoint ((v j : K →L[ℂ] K) (x j))=
      if i=j then x j else 0 := by
    by_cases hij : i=j
    · subst j
      have hh : (v i : K →L[ℂ] K).adjoint.comp (v i : K →L[ℂ] K)=ContinuousLinearMap.id ℂ K :=
        congrArg (fun a : P => (a:K →L[ℂ] K)) (by simpa using hv i i)
      simpa using congrArg (fun T : K →L[ℂ] K => T (x i)) hh
    · have hh : (v i : K →L[ℂ] K).adjoint.comp (v j : K →L[ℂ] K)=0 :=
        congrArg (fun a : P => (a:K →L[ℂ] K)) (by simpa only [ite_eq_right hij] using hv i j)
      simpa [hij] using congrArg (fun T : K →L[ℂ] K => T (x j)) hh
  simp only [he]
  simp

end Isometries

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.isometry_row_adjoint_comp_oai.{u} := @OAI.Kadison.isometry_row_adjoint_comp_oai.{u}
