-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:55:43.75935+00:00
-- url     : https://prove2.me/submissions/434950dc-fce7-4553-a2ff-487df5ea5bf5

import Mathlib
import Definitions.Def_OAIQ229C035
import Theorems.Thm_OAI_NuclearUltrapower_SOS_goodWord_mul_ca

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

theorem goodWord_mem {n : ℕ} {m : Mat3} (h : GoodWord n m) : interpret m ∈ elementary := by
  obtain ⟨_, w, hw, _, hs⟩ := h
  rw [← hw]
  exact elementary.list_prod_mem (fun g hg => Subgroup.subset_closure (hs g hg))

theorem eInterpret_coe {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    (eInterpret m : SL) = interpret m := by
  simp only [eInterpret, dite_eq_left (goodWord_mem h)]

theorem eInterpret_mul {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
    eInterpret (matMul a b) = eInterpret a * eInterpret b := by
  apply Subtype.ext
  change (eInterpret (matMul a b) : SL) = (eInterpret a : SL) * (eInterpret b : SL)
  rw [eInterpret_coe (goodWord_mul_ca ha hb), eInterpret_coe ha, eInterpret_coe hb,
    interpret_mul a b ha.1 hb.1]

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem value_mul_ca_oai (ρ : E →* unitary A) {n k : ℕ} (a b : Mat3)
    (ha : GoodWord n a) (hb : GoodWord k b) :
    value ρ (matMul a b) = value ρ a * value ρ b := by
  simp only [value, eInterpret_mul ha hb, map_mul, Submonoid.coe_mul]

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca_oai.{u_1}
