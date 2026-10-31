-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.residualRows_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:27:50.949521+00:00
-- url     : https://prove2.me/submissions/5300a71b-0a88-48fe-9984-d860573a6184

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_delta_good
import Theorems.Thm_OAI_NuclearUltrapower_SOS_gramPolyRow_good
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_mul
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_mul

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

theorem goodWord_mul {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
    GoodWord (n+k) (matMul a b) := by
  obtain ⟨had, wa, hwa, hla, hsa⟩ := ha
  obtain ⟨hbd, wb, hwb, hlb, hsb⟩ := hb
  refine ⟨by rw [toMatrix_mul, Matrix.det_mul, had, hbd, one_mul], wa ++ wb, ?_, ?_, ?_⟩
  · rw [List.prod_append, hwa, hwb, interpret_mul a b had hbd]
  · simp only [List.length_append]; omega
  · intro s hs
    exact (List.mem_append.mp hs).elim (hsa s) (hsb s)

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
open NuclearUltrapower.SL3Certificate

theorem residualRows_decomp : residualRows = residualRow0 :: residualRow1 ::
    (basis.zip gramData).map (fun p => gramPolyRow p.1 p.2) := by rfl

end NuclearUltrapower.SOS
end

section

namespace NuclearUltrapower.SOS

theorem residualRow0_good {p : Mat3 × ℤ} (hp : p ∈ residualRow0) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  obtain ⟨a,ha,hqa⟩ := List.mem_flatMap.mp hq
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hqa
  exact goodWord_mono (goodWord_mul (delta_good ha) (delta_good hb)) (by norm_num)

theorem residualRow1_good {p : Mat3 × ℤ} (hp : p ∈ residualRow1) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact goodWord_mono (delta_good (p := q) hq) (by norm_num)

theorem residualRows_good_oai {p : Mat3 × ℤ} (hp : p ∈ residualRows.flatten) : GoodWord 4 p.1 := by
  rw [residualRows_decomp] at hp
  simp only [List.flatten_cons, List.mem_append] at hp
  rcases hp with h | h | h
  · exact residualRow0_good h
  · exact residualRow1_good h
  · obtain ⟨r,hr,hp⟩ := List.mem_flatten.mp h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact gramPolyRow_good (List.of_mem_zip hq).1 q.2 hp

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.residualRows_good_oai := @OAI.NuclearUltrapower.SOS.residualRows_good_oai
