-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.goodWord_mul_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:15:49.7072+00:00
-- url     : https://prove2.me/submissions/4ab3c97b-a164-4bc3-b6b3-1fd173931a77

import Mathlib
import Definitions.Def_OAIQ229C035

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.Elementary.integralTheta_left _root_.OAI.NuclearUltrapower.Elementary.integralTheta_pow_translation _root_.OAI.NuclearUltrapower.Elementary.integralTheta_right _root_.OAI.NuclearUltrapower.Elementary.integralTheta_translation _root_.OAI.NuclearUltrapower.Elementary.residuePermutation_apply _root_.OAI.NuclearUltrapower.Elementary.residueUnitary_apply _root_.OAI.NuclearUltrapower.Elementary.residue_one _root_.OAI.NuclearUltrapower.Elementary.residue_theta _root_.OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem toMatrix_mul (a b : Mat3) : toMatrix (matMul a b) = toMatrix a * toMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, matMul, entry, Matrix.mul_apply, Fin.sum_univ_succ, List.range_succ, add_assoc]

theorem interpret_coe (m : Mat3) (h : (toMatrix m).det = 1) :
    (interpret m : Matrix (Fin 3) (Fin 3) ℤ) = toMatrix m := by
  simp [interpret, h]

theorem interpret_mul (a b : Mat3) (ha : (toMatrix a).det = 1) (hb : (toMatrix b).det = 1) :
    interpret (matMul a b) = interpret a * interpret b := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_mul, Matrix.det_mul, ha, hb, one_mul]),
    Matrix.SpecialLinearGroup.coe_mul, interpret_coe _ ha, interpret_coe _ hb, toMatrix_mul]

end NuclearUltrapower.SOS

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem goodWord_mul_ca_oai {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
    GoodWord (n+k) (matMul a b) := by
  obtain ⟨had, wa, hwa, hla, hsa⟩ := ha
  obtain ⟨hbd, wb, hwb, hlb, hsb⟩ := hb
  refine ⟨by rw [toMatrix_mul, Matrix.det_mul, had, hbd, one_mul], wa ++ wb, ?_, ?_, ?_⟩
  · rw [List.prod_append, hwa, hwb, interpret_mul a b had hbd]
  · simp only [List.length_append]; omega
  · intro s hs
    exact (List.mem_append.mp hs).elim (hsa s) (hsb s)

end NuclearUltrapower.SOS
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.goodWord_mul_ca_oai := @OAI.NuclearUltrapower.SOS.goodWord_mul_ca_oai
