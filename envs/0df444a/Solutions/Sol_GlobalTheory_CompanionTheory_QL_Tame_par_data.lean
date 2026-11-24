-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Tame.par_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:45:24.959343+00:00
-- url     : https://prove2.me/submissions/f303a976-8557-437d-a819-9deee2616f34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_congr_mod
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Tame_det_eq_blocks
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_localField_uniformizer_norm_properties
import Theorems.Thm_GlobalTheory_T_mem_integralGL_iff_integral_unit_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Tame
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Tame
theorem _root_.solution (h : LF O ϖ nrm q) {r c : ℕ} {k : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) :
    nrm (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    nrm (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    ∃ o ∈ O, (k : Matrix (Fin (r + c)) (Fin (r + c)) F).det -
      (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det *
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = ϖ * o := by
  obtain ⟨-, hϖ, hO, hlt, -, hult, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties h
  set M : Matrix (Fin (r + c)) (Fin (r + c)) F := (k : Matrix (Fin (r + c)) (Fin (r + c)) F) with hMdef
  have hM : IsInt O M := hk.1.1
  have hdet : nrm M.det = 1 := ((GlobalTheory.T.mem_integralGL_iff_integral_unit_det h (r + c) k).1 hk.1).2
  have hC := hk.2
  have hcong : ∃ o ∈ O, M.det - (bAA M).det * (bDD M).det = ϖ * o := by
    have := det_congr_mod O hϖ (Matrix.fromBlocks (bAA M) (bAD M) (bDA M) (bDD M))
      (Matrix.fromBlocks (bAA M) (bAD M) 0 (bDD M))
      (by rintro (i | i) (j | j) <;> exact hM _ _)
      (by
        rintro (i | i) (j | j)
        · exact hM _ _
        · exact hM _ _
        · exact O.zero_mem
        · exact hM _ _)
      (by
        rintro (i | i) (j | j)
        · exact ⟨0, O.zero_mem, by simp⟩
        · exact ⟨0, O.zero_mem, by simp⟩
        · obtain ⟨o, ho, e⟩ := hC i j
          exact ⟨o, ho, by simpa using e⟩
        · exact ⟨0, O.zero_mem, by simp⟩)
    rwa [← det_eq_blocks, Matrix.det_fromBlocks_zero₂₁] at this
  obtain ⟨o, ho, e⟩ := hcong
  have hA : nrm (bAA M).det ≤ 1 := (hO _).2 (det_mem O _ fun i j => hM _ _)
  have hD : nrm (bDD M).det ≤ 1 := (hO _).2 (det_mem O _ fun i j => hM _ _)
  have hsmall : nrm (ϖ * o) < 1 := (hlt _).2 ⟨o, ho, rfl⟩
  have hprod : 1 ≤ nrm (bAA M).det * nrm (bDD M).det := by
    have e2 : M.det = (bAA M).det * (bDD M).det + ϖ * o := by rw [← e]; ring
    have h3 := hult ((bAA M).det * (bDD M).det) (ϖ * o)
    rw [← e2, hdet, map_mul] at h3
    rcases le_max_iff.1 h3 with h4 | h4
    · exact h4
    · exact absurd h4 (not_le.2 hsmall)
  have hA0 : 0 ≤ nrm (bAA M).det := nrm.nonneg _
  have hD0 : 0 ≤ nrm (bDD M).det := nrm.nonneg _
  refine ⟨?_, ?_, o, ho, e⟩ <;> nlinarith
end GlobalTheory.CompanionTheory.QL.Tame
