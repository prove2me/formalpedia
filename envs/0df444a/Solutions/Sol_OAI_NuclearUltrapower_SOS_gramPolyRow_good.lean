-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.gramPolyRow_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:27:28.547582+00:00
-- url     : https://prove2.me/submissions/10cd466b-fa38-4692-823f-bbf86d09586b

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_basis_good
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_inv
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_mul
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_inv
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

theorem generators_det : ∀ m ∈ generators, (toMatrix m).det = 1 := by
  decide +kernel

theorem generators_inverse : ∀ m ∈ generators, matInv m ∈ generators := by
  decide +kernel

theorem genSet_inv {g : SL} (h : g ∈ genSet) : g⁻¹ ∈ genSet := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨matInv m, generators_inverse m hm, interpret_inv m (generators_det m hm)⟩

theorem goodWord_mul {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
    GoodWord (n+k) (matMul a b) := by
  obtain ⟨had, wa, hwa, hla, hsa⟩ := ha
  obtain ⟨hbd, wb, hwb, hlb, hsb⟩ := hb
  refine ⟨by rw [toMatrix_mul, Matrix.det_mul, had, hbd, one_mul], wa ++ wb, ?_, ?_, ?_⟩
  · rw [List.prod_append, hwa, hwb, interpret_mul a b had hbd]
  · simp only [List.length_append]; omega
  · intro s hs
    exact (List.mem_append.mp hs).elim (hsa s) (hsb s)

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

theorem gramPolyRow_good_oai {a : Mat3} (ha : a ∈ basis) (r : List ℤ)
    {p : Mat3 × ℤ} (hp : p ∈ gramPolyRow a r) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact goodWord_mul (goodWord_inv (basis_good ha)) (basis_good (List.of_mem_zip hq).1)

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.gramPolyRow_good_oai := @OAI.NuclearUltrapower.SOS.gramPolyRow_good_oai
