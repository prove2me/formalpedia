-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:24:30.098709+00:00
-- url     : https://prove2.me/submissions/97666d86-d648-4d8b-bf70-39ecb0094fb9

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_inv
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_inv

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

theorem generators_det : ∀ m ∈ generators, (toMatrix m).det = 1 := by
  decide +kernel

theorem generators_inverse : ∀ m ∈ generators, matInv m ∈ generators := by
  decide +kernel

theorem genSet_inv {g : SL} (h : g ∈ genSet) : g⁻¹ ∈ genSet := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨matInv m, generators_inverse m hm, interpret_inv m (generators_det m hm)⟩

theorem goodWord_inv {n : ℕ} {a : Mat3} (ha : GoodWord n a) : GoodWord n (matInv a) := by
  obtain ⟨had, w, hw, hl, hs⟩ := ha
  refine ⟨by rw [toMatrix_inv, Matrix.det_adjugate, had, one_pow], w.reverse.map Inv.inv, ?_, ?_, ?_⟩
  · rw [List.map_reverse, ← List.prod_inv_reverse, hw, interpret_inv a had]
  · simpa using hl
  · intro s hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
    exact genSet_inv (hs g (List.mem_reverse.mp hg))

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

theorem eInterpret_inv {n : ℕ} {a : Mat3} (ha : GoodWord n a) :
    eInterpret (matInv a) = (eInterpret a)⁻¹ := by
  apply Subtype.ext
  change (eInterpret (matInv a) : SL) = (eInterpret a : SL)⁻¹
  rw [eInterpret_coe (goodWord_inv ha), eInterpret_coe ha, interpret_inv a ha.1]

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem value_inv_oai (ρ : E →* unitary A) {n : ℕ} (a : Mat3) (ha : GoodWord n a) :
    value ρ (matInv a) = star (value ρ a) := by
  simp only [value, eInterpret_inv ha, map_inv]
  rfl

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv_oai.{u_1}
