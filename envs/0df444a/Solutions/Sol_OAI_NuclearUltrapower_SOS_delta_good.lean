-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.delta_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:25:59.829834+00:00
-- url     : https://prove2.me/submissions/84d0bb29-0934-4bfa-b884-6b32eebe183f

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_one
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_one

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

theorem goodWord_one : GoodWord 0 matOne := by
  refine ⟨by rw [toMatrix_one, Matrix.det_one], [], ?_, by simp, by simp⟩
  simp only [List.prod_nil, interpret_one]

theorem goodWord_generator {m : Mat3} (hm : m ∈ generators) : GoodWord 1 m := by
  refine ⟨generators_det m hm, [interpret m], by simp, by simp, ?_⟩
  intro s hs
  have : s = interpret m := by simpa using hs
  subst s
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩)

theorem goodWord_mono {n k : ℕ} {a : Mat3} (ha : GoodWord n a) (h : n ≤ k) : GoodWord k a := by
  obtain ⟨had, w, hw, hl, hs⟩ := ha
  exact ⟨had, w, hw, hl.trans h, hs⟩

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem delta_good_oai {p : Mat3 × ℤ} (hp : p ∈ delta) : GoodWord 1 p.1 := by
  simp only [delta, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨m, hm, rfl⟩
  · exact goodWord_mono goodWord_one (by norm_num)
  · exact goodWord_generator hm

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.delta_good_oai := @OAI.NuclearUltrapower.SOS.delta_good_oai
