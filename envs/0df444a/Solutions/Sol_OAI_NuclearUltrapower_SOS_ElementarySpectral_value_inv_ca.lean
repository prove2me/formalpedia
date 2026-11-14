-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:59:51.003301+00:00
-- url     : https://prove2.me/submissions/07d2c328-c61e-4145-b733-cf2907ed0ca7

import Mathlib
import Definitions.Def_OAIQ229C035
import Theorems.Thm_OAI_NuclearUltrapower_SOS_goodWord_inv_ca

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

theorem toMatrix_inv (a : Mat3) : toMatrix (matInv a) = (toMatrix a).adjugate := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, matInv, entry, List.range_succ] <;> ring

theorem interpret_coe (m : Mat3) (h : (toMatrix m).det = 1) :
    (interpret m : Matrix (Fin 3) (Fin 3) ℤ) = toMatrix m := by
  simp [interpret, h]

theorem interpret_inv (a : Mat3) (ha : (toMatrix a).det = 1) :
    interpret (matInv a) = (interpret a)⁻¹ := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_inv, Matrix.det_adjugate, ha, one_pow]),
    Matrix.SpecialLinearGroup.coe_inv, interpret_coe _ ha, toMatrix_inv]

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

theorem eInterpret_inv {n : ℕ} {a : Mat3} (ha : GoodWord n a) :
    eInterpret (matInv a) = (eInterpret a)⁻¹ := by
  apply Subtype.ext
  change (eInterpret (matInv a) : SL) = (eInterpret a : SL)⁻¹
  rw [eInterpret_coe (goodWord_inv_ca ha), eInterpret_coe ha, interpret_inv a ha.1]

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

theorem value_inv_ca_oai (ρ : E →* unitary A) {n : ℕ} (a : Mat3) (ha : GoodWord n a) :
    value ρ (matInv a) = star (value ρ a) := by
  simp only [value, eInterpret_inv ha, map_inv]
  rfl

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv_ca_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.value_inv_ca_oai.{u_1}
