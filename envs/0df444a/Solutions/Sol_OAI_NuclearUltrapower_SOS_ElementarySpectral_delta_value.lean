-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:18:33.47641+00:00
-- url     : https://prove2.me/submissions/d51055eb-24b5-43e7-be10-60bb67bc1210

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_genList_nodup
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_one
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_one

section
-- module Solutions.OAIQ019_Nuc.Compat
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem goodWord_one : GoodWord 0 matOne := by
  refine ⟨by rw [toMatrix_one, Matrix.det_one], [], ?_, by simp, by simp⟩
  simp only [List.prod_nil, interpret_one]

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem goodWord_mem {n : ℕ} {m : Mat3} (h : GoodWord n m) : interpret m ∈ elementary := by
  obtain ⟨_, w, hw, _, hs⟩ := h
  rw [← hw]
  exact elementary.list_prod_mem (fun g hg => Subgroup.subset_closure (hs g hg))

theorem eInterpret_coe {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    (eInterpret m : SL) = interpret m := by
  simp only [eInterpret, dite_eq_left (goodWord_mem h)]

@[simp] theorem eInterpret_one : eInterpret matOne = 1 := by
  apply Subtype.ext
  rw [eInterpret_coe goodWord_one, interpret_one]
  rfl

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Algebra
variable {A : Type*} [CStarAlgebra A]

@[simp] theorem value_one (ρ : E →* unitary A) : value ρ matOne = 1 := by
  simp [value, eInterpret_one]

theorem delta_value_oai (ρ : E →* unitary A) :
    eval (value ρ) delta = (12 : ℤ) • (1:A) - ∑ g ∈ eGenSet, (ρ g : A) := by
  rw [eGenSet, List.sum_toFinset _ genList_nodup]
  simp only [delta, eval, List.map_cons, List.map_map, Function.comp_def,
    List.sum_cons, neg_one_zsmul]
  rw [value_one]
  simp only [List.sum_neg, sub_eq_add_neg, value, List.map_map, Function.comp_def]

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_value_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_value_oai.{u_1}
