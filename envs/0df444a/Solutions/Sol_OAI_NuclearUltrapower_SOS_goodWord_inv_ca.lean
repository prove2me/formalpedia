-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.goodWord_inv_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:59:52.1189+00:00
-- url     : https://prove2.me/submissions/0d5d0f9d-d22c-4ef4-8481-011863a7deae

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
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.Elementary.integralTheta_left _root_.OAI.NuclearUltrapower.Elementary.integralTheta_pow_translation _root_.OAI.NuclearUltrapower.Elementary.integralTheta_right _root_.OAI.NuclearUltrapower.Elementary.integralTheta_translation _root_.OAI.NuclearUltrapower.Elementary.residuePermutation_apply _root_.OAI.NuclearUltrapower.Elementary.residueUnitary_apply _root_.OAI.NuclearUltrapower.Elementary.residue_one _root_.OAI.NuclearUltrapower.Elementary.residue_theta _root_.OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep_coe
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

theorem goodWord_inv_ca_oai {n : ℕ} {a : Mat3} (ha : GoodWord n a) : GoodWord n (matInv a) := by
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

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.goodWord_inv_ca_oai := @OAI.NuclearUltrapower.SOS.goodWord_inv_ca_oai
