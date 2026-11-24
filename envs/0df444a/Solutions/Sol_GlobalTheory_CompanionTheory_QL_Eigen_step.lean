-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:05:08.561659+00:00
-- url     : https://prove2.me/submissions/be5dbcf2-f051-4a03-9189-33bc90ff732d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_unramifiedCharExt_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_extendedCharacter_congr_of_tame
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_int_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_int_add
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_II_add
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_II_mul_int
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_int_mul_II
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_II_int
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_det_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_nrm_eq_one_of_close
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_Jset_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_BlockMul_blocks_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_extendedCharacter_congr_of_tame
import Theorems.Thm_GlobalTheory_T_parahoric_character_modulus_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Eigen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Eigen
theorem _root_.solution (hLF : LF O ϖ nrm q) (δ : Fˣ →* ℂˣ) (hδ : Del nrm δ) {r d c : ℕ}
    {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) {x : Matrix (Fin (r + d)) (Fin (r + c)) F}
    (hx : Supp O ϖ x) :
    Supp O ϖ (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) ∧
      chi0 δ (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det =
        chi0 δ (bAA x).det * chi0 δ (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det := by
  obtain ⟨-, hϖ, -, hlt, -, hna, -⟩ := NormalisedValue.main hLF
  obtain ⟨e1, e2, e3, e4⟩ := BlockMul.blocks_mul r d c c x (k : Matrix (Fin (r + c)) (Fin (r + c)) F)
  have kint : ∀ i j, (k : Matrix (Fin (r + c)) (Fin (r + c)) F) i j ∈ O := hk.1.1
  have ka : bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O r r := fun i j => kint _ _
  have kb : bAD (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O r c := fun i j => kint _ _
  have kd : bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ intMat O c c := fun i j => kint _ _
  have kc : bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ := hk.2
  obtain ⟨hA, hC, hB, hD⟩ := hx
  obtain ⟨hAi, hAd⟩ := (Jset_iff hLF _).1 hA
  have hadet : nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 :=
    ((GlobalTheory.T.parahoric_character_modulus_properties hLF δ hδ r c).2.1 k hk).2.1
  have hV := int_mul hAi ka
  have hW := int_mul_II hB kc
  have hU : bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) ∈ intMat O r r := by
    rw [e1]; exact int_add hV (II_int hϖ hW)
  have hdiff : bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) -
      bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F) ∈ IIset O ϖ := by
    rw [e1, add_sub_cancel_left]; exact hW
  obtain ⟨o, ho, hoe⟩ := det_congr hϖ hU hV hdiff
  have hVd : nrm (bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 := by
    rw [Matrix.det_mul, map_mul, hAd, hadet, one_mul]
  have hlt' := (hlt _).2 ⟨o, ho, hoe⟩
  have hUd := nrm_eq_one_of_close hna hVd hlt'
  have hUne : (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det ≠ 0 := fun h => by
    rw [h, map_zero] at hUd; exact zero_ne_one hUd
  have hVne : (bAA x * bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h => by
    rw [h, map_zero] at hVd; exact zero_ne_one hVd
  refine ⟨⟨(Jset_iff hLF _).2 ⟨hU, hUd⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [e3]; exact II_add (II_mul_int hC ka) (int_mul_II hD kc)
  · rw [e2]; exact int_add (int_mul hAi kb) (int_mul hB kd)
  · rw [e4]; exact int_add (int_mul (II_int hϖ hC) kb) (int_mul hD kd)
  · rw [extendedCharacter_congr_of_tame nrm δ hδ.tame hUne hVne (by rw [hVd]; exact hlt')]
    rw [Matrix.det_mul] at hVne ⊢
    exact unramifiedCharExt_mul δ (left_ne_zero_of_mul hVne) (right_ne_zero_of_mul hVne)
end GlobalTheory.CompanionTheory.QL.Eigen
