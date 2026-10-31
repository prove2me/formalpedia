-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.basis_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:25:36.946983+00:00
-- url     : https://prove2.me/submissions/4907e7a9-a993-462d-ac7b-4c99d1112363

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_mul
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_one
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_mul
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

theorem matrixWord_good (w : List Mat3) (hw : ∀ m ∈ w, m ∈ generators) :
    GoodWord w.length (matrixWord w) := by
  induction w with
  | nil => exact goodWord_one
  | cons a w ih =>
    have ha := goodWord_generator (hw a (by simp))
    have ht := ih (fun m hm => hw m (by simp [hm]))
    simpa only [List.length_cons, Nat.add_comm, matrixWord] using goodWord_mul ha ht

theorem basis_words : basisWords.map matrixWord = basis := by decide +kernel

theorem basisWords_length : ∀ w ∈ basisWords, w.length ≤ 2 := by decide +kernel

theorem basisWords_support : ∀ w ∈ basisWords, ∀ m ∈ w, m ∈ generators := by decide +kernel

theorem basis_good_oai {m : Mat3} (hm : m ∈ basis) : GoodWord 2 m := by
  rw [← basis_words] at hm
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  exact goodWord_mono (matrixWord_good w (basisWords_support w hw)) (basisWords_length w hw)

end NuclearUltrapower.SOS
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.basis_good_oai := @OAI.NuclearUltrapower.SOS.basis_good_oai
