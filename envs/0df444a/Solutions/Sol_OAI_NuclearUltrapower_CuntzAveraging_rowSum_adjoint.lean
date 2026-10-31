-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:03:06.302951+00:00
-- url     : https://prove2.me/submissions/2b9836c8-118c-4eac-9fba-b92f8c897f6d

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N039

section
-- module Solutions.OAIQ019_Nuc.Compat
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzWords
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzWords

/-- Orthogonality is a consequence of the two defining Cuntz relations. -/
theorem cross {D : Type*} [CStarAlgebra D] (r : Fin 2 → D) (hr : CuntzTwoRelations r)
    (i j : Fin 2) (hij : i ≠ j) : star (r i) * r j = 0 := by
  have hsum : r i * star (r i) + r j * star (r j) = 1 := by
    have h := hr.2
    fin_cases i <;> fin_cases j <;> try contradiction
    · simpa [Fin.sum_univ_two] using h
    · simpa [Fin.sum_univ_two,add_comm] using h
  have hh : star (r j) * (r i * star (r i) + r j * star (r j)) * r j = 1 := by
    rw [hsum,mul_one,hr.1]
  have he : star (star (r i) * r j) * (star (r i) * r j) = 0 := by
    simp only [mul_add,add_mul] at hh
    have ht : star (r j) * (r j * star (r j)) * r j = 1 := by
      simp only [← mul_assoc, hr.1, one_mul]
    rw [ht,add_eq_right] at hh
    simpa only [star_mul,star_star,mul_assoc] using hh
  exact (CStarRing.star_mul_self_eq_zero_iff _).mp he

end NuclearUltrapower.CuntzWords
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instDecidableEqIndex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

@[simp] theorem left_star_mul (i j : Fin 2) :
    star (left (H := H) i) * left j = if i = j then 1 else 0 := by
  change star (tensorLeftHom (shift i)) * tensorLeftHom (shift j) = _
  rw [← map_star,← map_mul]
  by_cases h : i = j
  · subst j
    rw [relations.1,map_one,ite_eq_left rfl]
  · rw [cross shift relations i j h,map_zero,ite_eq_right h]

end NuclearUltrapower.CuntzAveraging
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- The row recursion comes from word concatenation and the genuine model shifts. -/
theorem row_step (n : ℕ) : row R (n+1) =
    ∑ i : Fin 2, ((left i).comp (row R n)).comp (star (R (generator i))) := by
  ext x
  rw [row_apply]
  change (∑ w : Fin 2 × Word n, coordinate (index (n := n+1) w)
    (star (R (value generator (n := n+1) w)) x)) = _
  rw [Fintype.sum_prod_type]
  simp only [sum_apply,ContinuousLinearMap.comp_apply,row_apply,map_sum,value_succ,
    index_succ,left_coordinate,map_mul,star_mul,mul_apply_eq_comp]

/-- Exact finite-level intertwining of the adjoint generator in reverse. -/
theorem left_star_row_next (n : ℕ) (i : Fin 2) :
    (star (left i)).comp (row R (n+1)) = (row R n).comp (star (R (generator i))) := by
  rw [row_step]
  ext x
  simp only [ContinuousLinearMap.comp_apply,sum_apply,map_sum]
  rw [Finset.sum_eq_single i]
  · change (star (left (H := H) i) * left i : Target H →L[ℂ] Target H) (row R n (star (R (generator i)) x)) = _
    rw [left_star_mul,ite_eq_left rfl,one_apply_eq_self]
  · intro j _ hji
    change (star (left (H := H) i) * left j : Target H →L[ℂ] Target H) (row R n (star (R (generator j)) x)) = 0
    rw [left_star_mul,ite_eq_right (Ne.symm hji),zero_apply]
  · simp

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem range_telescope_rev {E : Type*} [AddCommGroup E] (f : ℕ → E) (N : ℕ) :
    ∑ k ∈ Finset.range N, (f (k+1) - f k) = f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; abel

/-- The adjoint generator has the same two-boundary estimate. -/
theorem rowSum_adjoint_oai (N : ℕ) (i : Fin 2) :
    (rowSum R N).comp (star (R (generator i))) - (star (left i)).comp (rowSum R N) =
      (star (left i)).comp ((row R N)-(row R 0)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,sub_apply,rowSum_apply,map_sum,map_sub]
  have he (k : ℕ) : row R k (star (R (generator i)) x) =
      star (left (H := H) i) (row R (k+1) x) :=
    congrArg (fun T : H →L[ℂ] Target H => T x) (left_star_row_next R k i).symm
  simp_rw [he]
  rw [← Finset.sum_sub_distrib]
  exact range_telescope_rev (fun k => star (left (H := H) i) (row R k x)) N

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint_oai.{u_1} := @OAI.NuclearUltrapower.CuntzAveraging.rowSum_adjoint_oai.{u_1}
