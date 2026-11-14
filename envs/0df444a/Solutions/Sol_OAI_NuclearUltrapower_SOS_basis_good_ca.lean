-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.basis_good_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:15:48.863469+00:00
-- url     : https://prove2.me/submissions/9c91a1d5-c570-4d9c-b926-52e8c0b2d6ee

import Mathlib
import Definitions.Def_OAIQ229C035
import Definitions.Def_OAIQ229C036
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

theorem toMatrix_one : toMatrix matOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem interpret_coe (m : Mat3) (h : (toMatrix m).det = 1) :
    (interpret m : Matrix (Fin 3) (Fin 3) ℤ) = toMatrix m := by
  simp [interpret, h]

theorem interpret_one : interpret matOne = 1 := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_one, Matrix.det_one]), toMatrix_one]
  rfl

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

theorem matrixWord_good (w : List Mat3) (hw : ∀ m ∈ w, m ∈ generators) :
    GoodWord w.length (matrixWord w) := by
  induction w with
  | nil => exact goodWord_one
  | cons a w ih =>
    have ha := goodWord_generator (hw a (by simp))
    have ht := ih (fun m hm => hw m (by simp [hm]))
    simpa only [List.length_cons, Nat.add_comm, matrixWord] using goodWord_mul_ca ha ht

theorem basis_words : basisWords.map matrixWord = basis := by decide +kernel

theorem basisWords_length : ∀ w ∈ basisWords, w.length ≤ 2 := by decide +kernel

theorem basisWords_support : ∀ w ∈ basisWords, ∀ m ∈ w, m ∈ generators := by decide +kernel

theorem basis_good_ca_oai {m : Mat3} (hm : m ∈ basis) : GoodWord 2 m := by
  rw [← basis_words] at hm
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  exact goodWord_mono (matrixWord_good w (basisWords_support w hw)) (basisWords_length w hw)

end NuclearUltrapower.SOS
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.basis_good_ca_oai := @OAI.NuclearUltrapower.SOS.basis_good_ca_oai
